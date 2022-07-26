//===-- RISCIVISelDAGToDAG.cpp - A dag to dag inst selector -------- ------===//
//
// wording by harihitode
//
// original license
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines an instruction selector for the RISCIV target.
//
//===----------------------------------------------------------------------===//

#include "RISCIVISelDAGToDAG.h"
#include "MCTargetDesc/RISCIVMCTargetDesc.h"
#include "MCTargetDesc/RISCIVMatInt.h"
#include "RISCIVISelLowering.h"
#include "RISCIVMachineFunctionInfo.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "risciv-isel"

namespace llvm {
namespace RISCIV {
#include "RISCIVGenSearchableTables.inc"
} // namespace RISCIV
} // namespace llvm

void RISCIVDAGToDAGISel::PostprocessISelDAG() {
  doPeepholeLoadStoreADDI();
}

static SDNode *selectImm(SelectionDAG *CurDAG, const SDLoc &DL, int64_t Imm,
                         const RISCIVSubtarget &Subtarget) {
  MVT XLenVT = Subtarget.getXLenVT();
  RISCIVMatInt::InstSeq Seq =
      RISCIVMatInt::generateInstSeq(Imm, Subtarget.getFeatureBits());

  SDNode *Result = nullptr;
  SDValue SrcReg = CurDAG->getRegister(RISCIV::X0, XLenVT);
  for (RISCIVMatInt::Inst &Inst : Seq) {
    SDValue SDImm = CurDAG->getTargetConstant(Inst.Imm, DL, XLenVT);
    if (Inst.Opc == RISCIV::LUI)
      Result = CurDAG->getMachineNode(RISCIV::LUI, DL, XLenVT, SDImm);
    else
      Result = CurDAG->getMachineNode(Inst.Opc, DL, XLenVT, SrcReg, SDImm);

    // Only the first instruction has X0 as its source.
    SrcReg = SDValue(Result, 0);
  }

  return Result;
}

void RISCIVDAGToDAGISel::Select(SDNode *Node) {
  // If we have a custom node, we have already selected.
  if (Node->isMachineOpcode()) {
    LLVM_DEBUG(dbgs() << "== "; Node->dump(CurDAG); dbgs() << "\n");
    Node->setNodeId(-1);
    return;
  }

  // Instruction Selection not handled by the auto-generated tablegen selection
  // should be handled here.
  unsigned Opcode = Node->getOpcode();
  MVT XLenVT = Subtarget->getXLenVT();
  SDLoc DL(Node);
  MVT VT = Node->getSimpleValueType(0);

  switch (Opcode) {
  case ISD::Constant: {
    auto *ConstNode = cast<ConstantSDNode>(Node);
    if (VT == XLenVT && ConstNode->isNullValue()) {
      SDValue New =
          CurDAG->getCopyFromReg(CurDAG->getEntryNode(), DL, RISCIV::X0, XLenVT);
      ReplaceNode(Node, New.getNode());
      return;
    }
    ReplaceNode(Node,
                selectImm(CurDAG, DL, ConstNode->getSExtValue(), *Subtarget));
    return;
  }
  case ISD::FrameIndex: {
    SDValue Imm = CurDAG->getTargetConstant(0, DL, XLenVT);
    int FI = cast<FrameIndexSDNode>(Node)->getIndex();
    SDValue TFI = CurDAG->getTargetFrameIndex(FI, VT);
    ReplaceNode(Node, CurDAG->getMachineNode(RISCIV::ADDI, DL, VT, TFI, Imm));
    return;
  }
  case ISD::SRL: {
    // We don't need this transform if zext.h is supported.
    if (Subtarget->hasStdExtZbb() || Subtarget->hasStdExtZbp())
      break;
    // Optimize (srl (and X, 0xffff), C) ->
    //          (srli (slli X, (XLen-16), (XLen-16) + C)
    // Taking into account that the 0xffff may have had lower bits unset by
    // SimplifyDemandedBits. This avoids materializing the 0xffff immediate.
    // This pattern occurs when type legalizing i16 right shifts.
    // FIXME: This could be extended to other AND masks.
    auto *N1C = dyn_cast<ConstantSDNode>(Node->getOperand(1));
    if (N1C) {
      uint64_t ShAmt = N1C->getZExtValue();
      SDValue N0 = Node->getOperand(0);
      if (ShAmt < 16 && N0.getOpcode() == ISD::AND && N0.hasOneUse() &&
          isa<ConstantSDNode>(N0.getOperand(1))) {
        uint64_t Mask = N0.getConstantOperandVal(1);
        Mask |= maskTrailingOnes<uint64_t>(ShAmt);
        if (Mask == 0xffff) {
          unsigned LShAmt = Subtarget->getXLen() - 16;
          SDNode *SLLI =
              CurDAG->getMachineNode(RISCIV::SLLI, DL, VT, N0->getOperand(0),
                                     CurDAG->getTargetConstant(LShAmt, DL, VT));
          SDNode *SRLI = CurDAG->getMachineNode(
              RISCIV::SRLI, DL, VT, SDValue(SLLI, 0),
              CurDAG->getTargetConstant(LShAmt + ShAmt, DL, VT));
          ReplaceNode(Node, SRLI);
          return;
        }
      }
    }

    break;
  }
  case ISD::AND: {
    auto *N1C = dyn_cast<ConstantSDNode>(Node->getOperand(1));
    if (!N1C)
      break;

    SDValue N0 = Node->getOperand(0);

    bool LeftShift = N0.getOpcode() == ISD::SHL;
    if (!LeftShift && N0.getOpcode() != ISD::SRL)
      break;

    auto *C = dyn_cast<ConstantSDNode>(N0.getOperand(1));
    if (!C)
      break;
    uint64_t C2 = C->getZExtValue();
    unsigned XLen = Subtarget->getXLen();
    if (!C2 || C2 >= XLen)
      break;

    uint64_t C1 = N1C->getZExtValue();

    // Clear irrelevant bits in the mask.
    if (LeftShift)
      C1 &= maskTrailingZeros<uint64_t>(C2);
    else
      C1 &= maskTrailingOnes<uint64_t>(XLen - C2);
    break;
  }
  case ISD::BITCAST: {
    MVT SrcVT = Node->getOperand(0).getSimpleValueType();
    // Just drop bitcasts between vectors if both are fixed or both are
    // scalable.
    if ((VT.isScalableVector() && SrcVT.isScalableVector()) ||
        (VT.isFixedLengthVector() && SrcVT.isFixedLengthVector())) {
      ReplaceUses(SDValue(Node, 0), Node->getOperand(0));
      CurDAG->RemoveDeadNode(Node);
      return;
    }
    break;
  }
  }

  // Select the default instruction.
  SelectCode(Node);
}

bool RISCIVDAGToDAGISel::SelectInlineAsmMemoryOperand(
    const SDValue &Op, unsigned ConstraintID, std::vector<SDValue> &OutOps) {
  switch (ConstraintID) {
  case InlineAsm::Constraint_m:
    // We just support simple memory operands that have a single address
    // operand and need no special handling.
    OutOps.push_back(Op);
    return false;
  case InlineAsm::Constraint_A:
    OutOps.push_back(Op);
    return false;
  default:
    break;
  }

  return true;
}

bool RISCIVDAGToDAGISel::SelectAddrFI(SDValue Addr, SDValue &Base) {
  if (auto *FIN = dyn_cast<FrameIndexSDNode>(Addr)) {
    Base = CurDAG->getTargetFrameIndex(FIN->getIndex(), Subtarget->getXLenVT());
    return true;
  }
  return false;
}

bool RISCIVDAGToDAGISel::SelectBaseAddr(SDValue Addr, SDValue &Base) {
  // If this is FrameIndex, select it directly. Otherwise just let it get
  // selected to a register independently.
  if (auto *FIN = dyn_cast<FrameIndexSDNode>(Addr))
    Base = CurDAG->getTargetFrameIndex(FIN->getIndex(), Subtarget->getXLenVT());
  else
    Base = Addr;
  return true;
}

bool RISCIVDAGToDAGISel::selectShiftMask(SDValue N, unsigned ShiftWidth,
                                        SDValue &ShAmt) {
  // Shift instructions on RISCIV only read the lower 5 or 6 bits of the shift
  // amount. If there is an AND on the shift amount, we can bypass it if it
  // doesn't affect any of those bits.
  if (N.getOpcode() == ISD::AND && isa<ConstantSDNode>(N.getOperand(1))) {
    const APInt &AndMask = N->getConstantOperandAPInt(1);

    // Since the max shift amount is a power of 2 we can subtract 1 to make a
    // mask that covers the bits needed to represent all shift amounts.
    assert(isPowerOf2_32(ShiftWidth) && "Unexpected max shift amount!");
    APInt ShMask(AndMask.getBitWidth(), ShiftWidth - 1);

    if (ShMask.isSubsetOf(AndMask)) {
      ShAmt = N.getOperand(0);
      return true;
    }

    // SimplifyDemandedBits may have optimized the mask so try restoring any
    // bits that are known zero.
    KnownBits Known = CurDAG->computeKnownBits(N->getOperand(0));
    if (ShMask.isSubsetOf(AndMask | Known.Zero)) {
      ShAmt = N.getOperand(0);
      return true;
    }
  }

  ShAmt = N;
  return true;
}

bool RISCIVDAGToDAGISel::selectSExti32(SDValue N, SDValue &Val) {
  if (N.getOpcode() == ISD::SIGN_EXTEND_INREG &&
      cast<VTSDNode>(N.getOperand(1))->getVT() == MVT::i32) {
    Val = N.getOperand(0);
    return true;
  }
  MVT VT = N.getSimpleValueType();
  if (CurDAG->ComputeNumSignBits(N) > (VT.getSizeInBits() - 32)) {
    Val = N;
    return true;
  }

  return false;
}

bool RISCIVDAGToDAGISel::selectZExti32(SDValue N, SDValue &Val) {
  if (N.getOpcode() == ISD::AND) {
    auto *C = dyn_cast<ConstantSDNode>(N.getOperand(1));
    if (C && C->getZExtValue() == UINT64_C(0xFFFFFFFF)) {
      Val = N.getOperand(0);
      return true;
    }
  }
  MVT VT = N.getSimpleValueType();
  APInt Mask = APInt::getHighBitsSet(VT.getSizeInBits(), 32);
  if (CurDAG->MaskedValueIsZero(N, Mask)) {
    Val = N;
    return true;
  }

  return false;
}

using ValidateFn = bool (*)(int64_t);

bool RISCIVDAGToDAGISel::selectRVVSimm5(SDValue N, unsigned Width,
                                        SDValue &Imm) {
  if (auto *C = dyn_cast<ConstantSDNode>(N)) {
    int64_t ImmVal = SignExtend64(C->getSExtValue(), Width);

    if (!isInt<5>(ImmVal))
      return false;

    Imm = CurDAG->getTargetConstant(ImmVal, SDLoc(N), Subtarget->getXLenVT());
    return true;
  }

  return false;
}

// Merge an ADDI into the offset of a load/store instruction where possible.
// (load (addi base, off1), off2) -> (load base, off1+off2)
// (store val, (addi base, off1), off2) -> (store val, base, off1+off2)
// This is possible when off1+off2 fits a 12-bit immediate.
void RISCIVDAGToDAGISel::doPeepholeLoadStoreADDI() {
  SelectionDAG::allnodes_iterator Position(CurDAG->getRoot().getNode());
  ++Position;

  while (Position != CurDAG->allnodes_begin()) {
    SDNode *N = &*--Position;
    // Skip dead nodes and any non-machine opcodes.
    if (N->use_empty() || !N->isMachineOpcode())
      continue;

    int OffsetOpIdx;
    int BaseOpIdx;

    // Only attempt this optimisation for I-type loads and S-type stores.
    switch (N->getMachineOpcode()) {
    default:
      continue;
    case RISCIV::LB:
    case RISCIV::LH:
    case RISCIV::LW:
    case RISCIV::LBU:
    case RISCIV::LHU:
      BaseOpIdx = 0;
      OffsetOpIdx = 1;
      break;
    case RISCIV::SB:
    case RISCIV::SH:
    case RISCIV::SW:
      BaseOpIdx = 1;
      OffsetOpIdx = 2;
      break;
    }

    if (!isa<ConstantSDNode>(N->getOperand(OffsetOpIdx)))
      continue;

    SDValue Base = N->getOperand(BaseOpIdx);

    // If the base is an ADDI, we can merge it in to the load/store.
    if (!Base.isMachineOpcode() || Base.getMachineOpcode() != RISCIV::ADDI)
      continue;

    SDValue ImmOperand = Base.getOperand(1);
    uint64_t Offset2 = N->getConstantOperandVal(OffsetOpIdx);

    if (auto *Const = dyn_cast<ConstantSDNode>(ImmOperand)) {
      int64_t Offset1 = Const->getSExtValue();
      int64_t CombinedOffset = Offset1 + Offset2;
      if (!isInt<12>(CombinedOffset))
        continue;
      ImmOperand = CurDAG->getTargetConstant(CombinedOffset, SDLoc(ImmOperand),
                                             ImmOperand.getValueType());
    } else if (auto *GA = dyn_cast<GlobalAddressSDNode>(ImmOperand)) {
      // If the off1 in (addi base, off1) is a global variable's address (its
      // low part, really), then we can rely on the alignment of that variable
      // to provide a margin of safety before off1 can overflow the 12 bits.
      // Check if off2 falls within that margin; if so off1+off2 can't overflow.
      const DataLayout &DL = CurDAG->getDataLayout();
      Align Alignment = GA->getGlobal()->getPointerAlignment(DL);
      if (Offset2 != 0 && Alignment <= Offset2)
        continue;
      int64_t Offset1 = GA->getOffset();
      int64_t CombinedOffset = Offset1 + Offset2;
      ImmOperand = CurDAG->getTargetGlobalAddress(
          GA->getGlobal(), SDLoc(ImmOperand), ImmOperand.getValueType(),
          CombinedOffset, GA->getTargetFlags());
    } else if (auto *CP = dyn_cast<ConstantPoolSDNode>(ImmOperand)) {
      // Ditto.
      Align Alignment = CP->getAlign();
      if (Offset2 != 0 && Alignment <= Offset2)
        continue;
      int64_t Offset1 = CP->getOffset();
      int64_t CombinedOffset = Offset1 + Offset2;
      ImmOperand = CurDAG->getTargetConstantPool(
          CP->getConstVal(), ImmOperand.getValueType(), CP->getAlign(),
          CombinedOffset, CP->getTargetFlags());
    } else {
      continue;
    }

    LLVM_DEBUG(dbgs() << "Folding add-immediate into mem-op:\nBase:    ");
    LLVM_DEBUG(Base->dump(CurDAG));
    LLVM_DEBUG(dbgs() << "\nN: ");
    LLVM_DEBUG(N->dump(CurDAG));
    LLVM_DEBUG(dbgs() << "\n");

    // Modify the offset operand of the load/store.
    if (BaseOpIdx == 0) // Load
      CurDAG->UpdateNodeOperands(N, Base.getOperand(0), ImmOperand,
                                 N->getOperand(2));
    else // Store
      CurDAG->UpdateNodeOperands(N, N->getOperand(0), Base.getOperand(0),
                                 ImmOperand, N->getOperand(3));

    // The add-immediate may now be dead, in which case remove it.
    if (Base.getNode()->use_empty())
      CurDAG->RemoveDeadNode(Base.getNode());
  }
}

// This pass converts a legalized DAG into a RISCIV-specific DAG, ready
// for instruction scheduling.
FunctionPass *llvm::createRISCIVISelDag(RISCIVTargetMachine &TM) {
  return new RISCIVDAGToDAGISel(TM);
}
