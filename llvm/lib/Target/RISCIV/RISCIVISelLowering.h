//===-- RISCIVISelLowering.h - DAG Lowering Interface -----------*- C++ -*-===//
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
// This file defines the interfaces to lower LLVM code into a selection DAG.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_RISCIV_RISCIVISELLOWERING_H
#define LLVM_LIB_TARGET_RISCIV_RISCIVISELLOWERING_H

#include "RISCIV.h"
#include "llvm/CodeGen/CallingConvLower.h"
#include "llvm/CodeGen/SelectionDAG.h"
#include "llvm/CodeGen/TargetLowering.h"

namespace llvm {
class RISCIVSubtarget;
struct RISCIVRegisterInfo;
namespace RISCIVISD {
enum NodeType : unsigned {
  FIRST_NUMBER = ISD::BUILTIN_OP_END,
  RET_FLAG,
  CALL,
  /// Select with condition operator - This selects between a true value and
  /// a false value (ops #3 and #4) based on the boolean result of comparing
  /// the lhs and rhs (ops #0 and #1) of a conditional expression with the
  /// condition code in op #2, a XLenVT constant from the ISD::CondCode enum.
  /// The lhs and rhs are XLenVT integers. The true and false values can be
  /// integer or floating point.
  SELECT_CC,
  BR_CC,
  BuildPairF64,
  SplitF64,
  TAIL,
  // Multiply high for signedxunsigned.
  MULHSU,
  // 32-bit operations from RV64M that can't be simply matched with a pattern
  // at instruction selection time. These have undefined behavior for division
  // by 0 or overflow (divw) like their target independent counterparts.
  DIVW,
  DIVUW,
  REMUW,
  // READ_CYCLE_WIDE - A read of the 64-bit cycle CSR on a 32-bit target
  // (returns (Lo, Hi)). It takes a chain operand.
  READ_CYCLE_WIDE,
  // Generalized Reverse and Generalized Or-Combine - directly matching the
  // semantics of the named RISC-V instructions. Lowered as custom nodes as
  // TableGen chokes when faced with commutative permutations in deeply-nested
  // DAGs. Each node takes an input operand and a control operand and outputs a
  // bit-manipulated version of input. All operands are i32 or XLenVT.
  GREV,
  GREVW,
  GORC,
  GORCW,
  SHFL,
  SHFLW,
  UNSHFL,
  UNSHFLW,
  // Reads value of CSR.
  // The first operand is a chain pointer. The second specifies address of the
  // required CSR. Two results are produced, the read value and the new chain
  // pointer.
  READ_CSR,
  // Write value to CSR.
  // The first operand is a chain pointer, the second specifies address of the
  // required CSR and the third is the value to write. The result is the new
  // chain pointer.
  WRITE_CSR,
  // Read and write value of CSR.
  // The first operand is a chain pointer, the second specifies address of the
  // required CSR and the third is the value to write. Two results are produced,
  // the value read before the modification and the new chain pointer.
  SWAP_CSR,

  // Memory opcodes start here.
  VLE_VL = ISD::FIRST_TARGET_MEMORY_OPCODE,
  VSE_VL,

  // WARNING: Do not add anything in the end unless you want the node to
  // have memop! In fact, starting from FIRST_TARGET_MEMORY_OPCODE all
  // opcodes will be thought as target memory ops!
};
} // namespace RISCIVISD

class RISCIVTargetLowering : public TargetLowering {
  const RISCIVSubtarget &Subtarget;

public:
  explicit RISCIVTargetLowering(const TargetMachine &TM,
                               const RISCIVSubtarget &STI);

  const RISCIVSubtarget &getSubtarget() const { return Subtarget; }

  bool isLegalAddressingMode(const DataLayout &DL, const AddrMode &AM, Type *Ty,
                             unsigned AS,
                             Instruction *I = nullptr) const override;
  bool isLegalICmpImmediate(int64_t Imm) const override;
  bool isLegalAddImmediate(int64_t Imm) const override;
  bool isTruncateFree(Type *SrcTy, Type *DstTy) const override;
  bool isTruncateFree(EVT SrcVT, EVT DstVT) const override;
  bool isZExtFree(SDValue Val, EVT VT2) const override;
  bool isSExtCheaperThanZExt(EVT SrcVT, EVT DstVT) const override;
  bool isCheapToSpeculateCttz() const override;
  bool isCheapToSpeculateCtlz() const override;
  bool isFPImmLegal(const APFloat &Imm, EVT VT,
                    bool ForCodeSize) const override;

  /// Return the register type for a given MVT, ensuring vectors are treated
  /// as a series of gpr sized integers.
  MVT getRegisterTypeForCallingConv(LLVMContext &Context, CallingConv::ID CC,
                                    EVT VT) const override;

  /// Return the number of registers for a given MVT, ensuring vectors are
  /// treated as a series of gpr sized integers.
  unsigned getNumRegistersForCallingConv(LLVMContext &Context,
                                         CallingConv::ID CC,
                                         EVT VT) const override;

  bool hasBitPreservingFPLogic(EVT VT) const override;

  // Provide custom lowering hooks for some operations.
  SDValue LowerOperation(SDValue Op, SelectionDAG &DAG) const override;
  void ReplaceNodeResults(SDNode *N, SmallVectorImpl<SDValue> &Results,
                          SelectionDAG &DAG) const override;

  bool targetShrinkDemandedConstant(SDValue Op, const APInt &DemandedBits,
                                    const APInt &DemandedElts,
                                    TargetLoweringOpt &TLO) const override;

  // This method returns the name of a target specific DAG node.
  const char *getTargetNodeName(unsigned Opcode) const override;

  ConstraintType getConstraintType(StringRef Constraint) const override;

  unsigned getInlineAsmMemConstraint(StringRef ConstraintCode) const override;

  std::pair<unsigned, const TargetRegisterClass *>
  getRegForInlineAsmConstraint(const TargetRegisterInfo *TRI,
                               StringRef Constraint, MVT VT) const override;

  void LowerAsmOperandForConstraint(SDValue Op, std::string &Constraint,
                                    std::vector<SDValue> &Ops,
                                    SelectionDAG &DAG) const override;

  MachineBasicBlock *
  EmitInstrWithCustomInserter(MachineInstr &MI,
                              MachineBasicBlock *BB) const override;

  EVT getSetCCResultType(const DataLayout &DL, LLVMContext &Context,
                         EVT VT) const override;

  bool convertSetCCLogicToBitwiseLogic(EVT VT) const override {
    return VT.isScalarInteger();
  }
  bool convertSelectOfConstantsToMath(EVT VT) const override { return true; }

  bool shouldInsertFencesForAtomic(const Instruction *I) const override {
    return isa<LoadInst>(I) || isa<StoreInst>(I);
  }
  Instruction *emitLeadingFence(IRBuilderBase &Builder, Instruction *Inst,
                                AtomicOrdering Ord) const override;
  Instruction *emitTrailingFence(IRBuilderBase &Builder, Instruction *Inst,
                                 AtomicOrdering Ord) const override;

  ISD::NodeType getExtendForAtomicOps() const override {
    return ISD::SIGN_EXTEND;
  }

  ISD::NodeType getExtendForAtomicCmpSwapArg() const override {
    return ISD::SIGN_EXTEND;
  }

  bool shouldExpandShift(SelectionDAG &DAG, SDNode *N) const override {
    if (DAG.getMachineFunction().getFunction().hasMinSize())
      return false;
    return true;
  }
  bool isDesirableToCommuteWithShift(const SDNode *N,
                                     CombineLevel Level) const override;

  /// If a physical register, this returns the register that receives the
  /// exception address on entry to an EH pad.
  Register
  getExceptionPointerRegister(const Constant *PersonalityFn) const override;

  /// If a physical register, this returns the register that receives the
  /// exception typeid on entry to a landing pad.
  Register
  getExceptionSelectorRegister(const Constant *PersonalityFn) const override;

  bool shouldExtendTypeInLibCall(EVT Type) const override;
  bool shouldSignExtendTypeInLibCall(EVT Type, bool IsSigned) const override;

  /// Returns the register with the specified architectural or ABI name. This
  /// method is necessary to lower the llvm.read_register.* and
  /// llvm.write_register.* intrinsics. Allocatable registers must be reserved
  /// with the clang -ffixed-xX flag for access to be allowed.
  Register getRegisterByName(const char *RegName, LLT VT,
                             const MachineFunction &MF) const override;

  // Lower incoming arguments, copy physregs into vregs
  SDValue LowerFormalArguments(SDValue Chain, CallingConv::ID CallConv,
                               bool IsVarArg,
                               const SmallVectorImpl<ISD::InputArg> &Ins,
                               const SDLoc &DL, SelectionDAG &DAG,
                               SmallVectorImpl<SDValue> &InVals) const override;
  bool CanLowerReturn(CallingConv::ID CallConv, MachineFunction &MF,
                      bool IsVarArg,
                      const SmallVectorImpl<ISD::OutputArg> &Outs,
                      LLVMContext &Context) const override;
  SDValue LowerReturn(SDValue Chain, CallingConv::ID CallConv, bool IsVarArg,
                      const SmallVectorImpl<ISD::OutputArg> &Outs,
                      const SmallVectorImpl<SDValue> &OutVals, const SDLoc &DL,
                      SelectionDAG &DAG) const override;
  SDValue LowerCall(TargetLowering::CallLoweringInfo &CLI,
                    SmallVectorImpl<SDValue> &InVals) const override;

  bool shouldConvertConstantLoadToIntImm(const APInt &Imm,
                                         Type *Ty) const override {
    return true;
  }
  bool mayBeEmittedAsTailCall(const CallInst *CI) const override;
  bool shouldConsiderGEPOffsetSplit() const override { return true; }

  bool decomposeMulByConstant(LLVMContext &Context, EVT VT,
                              SDValue C) const override;

  /// Returns true if the target allows unaligned memory accesses of the
  /// specified type.
  bool allowsMisalignedMemoryAccesses(
      EVT VT, unsigned AddrSpace = 0, Align Alignment = Align(1),
      MachineMemOperand::Flags Flags = MachineMemOperand::MONone,
      bool *Fast = nullptr) const override;

  bool splitValueIntoRegisterParts(SelectionDAG &DAG, const SDLoc &DL,
                                   SDValue Val, SDValue *Parts,
                                   unsigned NumParts, MVT PartVT,
                                   Optional<CallingConv::ID> CC) const override;

  SDValue
  joinRegisterPartsIntoValue(SelectionDAG &DAG, const SDLoc &DL,
                             const SDValue *Parts, unsigned NumParts,
                             MVT PartVT, EVT ValueVT,
                             Optional<CallingConv::ID> CC) const override;

  static RISCIVII::VLMUL getLMUL(MVT VT);
  static unsigned getRegClassIDForLMUL(RISCIVII::VLMUL LMul);
  static unsigned getSubregIndexByMVT(MVT VT, unsigned Index);
  static unsigned getRegClassIDForVecVT(MVT VT);
  static std::pair<unsigned, unsigned>
  decomposeSubvectorInsertExtractToSubRegs(MVT VecVT, MVT SubVecVT,
                                           unsigned InsertExtractIdx,
                                           const RISCIVRegisterInfo *TRI);
  MVT getContainerForFixedLengthVector(MVT VT) const;

  bool shouldRemoveExtendFromGSIndex(EVT VT) const override;

private:
  /// RISCIVCCAssignFn - This target-specific function extends the default
  /// CCValAssign with additional information used to lower RISC-V calling
  /// conventions.
  typedef bool RISCIVCCAssignFn(const DataLayout &DL, RISCIVABI::ABI,
                               unsigned ValNo, MVT ValVT, MVT LocVT,
                               CCValAssign::LocInfo LocInfo,
                               ISD::ArgFlagsTy ArgFlags, CCState &State,
                               bool IsFixed, bool IsRet, Type *OrigTy,
                               const RISCIVTargetLowering &TLI,
                               Optional<unsigned> FirstMaskArgument);

  void analyzeInputArgs(MachineFunction &MF, CCState &CCInfo,
                        const SmallVectorImpl<ISD::InputArg> &Ins, bool IsRet,
                        RISCIVCCAssignFn Fn) const;
  void analyzeOutputArgs(MachineFunction &MF, CCState &CCInfo,
                         const SmallVectorImpl<ISD::OutputArg> &Outs,
                         bool IsRet, CallLoweringInfo *CLI,
                         RISCIVCCAssignFn Fn) const;

  template <class NodeTy>
  SDValue getAddr(NodeTy *N, SelectionDAG &DAG, bool IsLocal = true) const;

  SDValue getStaticTLSAddr(GlobalAddressSDNode *N, SelectionDAG &DAG,
                           bool UseGOT) const;
  SDValue getDynamicTLSAddr(GlobalAddressSDNode *N, SelectionDAG &DAG) const;

  SDValue lowerGlobalAddress(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerBlockAddress(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerConstantPool(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerJumpTable(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerGlobalTLSAddress(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerSELECT(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerBRCOND(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerVASTART(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFRAMEADDR(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerRETURNADDR(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerShiftLeftParts(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerShiftRightParts(SDValue Op, SelectionDAG &DAG, bool IsSRA) const;
  SDValue lowerSPLAT_VECTOR_PARTS(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerVectorMaskSplat(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerVectorMaskExt(SDValue Op, SelectionDAG &DAG,
                             int64_t ExtTrueVal) const;
  SDValue lowerVectorMaskTrunc(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerINSERT_VECTOR_ELT(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerEXTRACT_VECTOR_ELT(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerINTRINSIC_WO_CHAIN(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerINTRINSIC_W_CHAIN(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerVECREDUCE(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerVectorMaskVECREDUCE(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFPVECREDUCE(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerINSERT_SUBVECTOR(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerEXTRACT_SUBVECTOR(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerSTEP_VECTOR(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerVECTOR_REVERSE(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerABS(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerMLOAD(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerMSTORE(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFixedLengthVectorFCOPYSIGNToRVV(SDValue Op,
                                               SelectionDAG &DAG) const;
  SDValue lowerMGATHER(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerMSCATTER(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFixedLengthVectorLoadToRVV(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFixedLengthVectorStoreToRVV(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFixedLengthVectorSetccToRVV(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFixedLengthVectorLogicOpToRVV(SDValue Op, SelectionDAG &DAG,
                                             unsigned MaskOpc,
                                             unsigned VecOpc) const;
  SDValue lowerFixedLengthVectorShiftToRVV(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerFixedLengthVectorSelectToRVV(SDValue Op,
                                            SelectionDAG &DAG) const;
  SDValue lowerToScalableOp(SDValue Op, SelectionDAG &DAG, unsigned NewOpc,
                            bool HasMask = true) const;
  SDValue lowerVPOp(SDValue Op, SelectionDAG &DAG, unsigned RISCIVISDOpc) const;
  SDValue lowerFixedLengthVectorExtendToRVV(SDValue Op, SelectionDAG &DAG,
                                            unsigned ExtendOpc) const;
  SDValue lowerGET_ROUNDING(SDValue Op, SelectionDAG &DAG) const;
  SDValue lowerSET_ROUNDING(SDValue Op, SelectionDAG &DAG) const;

  SDValue expandUnalignedRVVLoad(SDValue Op, SelectionDAG &DAG) const;
  SDValue expandUnalignedRVVStore(SDValue Op, SelectionDAG &DAG) const;

  bool isEligibleForTailCallOptimization(
      CCState &CCInfo, CallLoweringInfo &CLI, MachineFunction &MF,
      const SmallVector<CCValAssign, 16> &ArgLocs) const;

  /// Generate error diagnostics if any register used by CC has been marked
  /// reserved.
  void validateCCReservedRegs(
      const SmallVectorImpl<std::pair<llvm::Register, llvm::SDValue>> &Regs,
      MachineFunction &MF) const;

  bool useRVVForFixedLengthVectorVT(MVT VT) const;

  MVT getVPExplicitVectorLengthTy() const override;
};

namespace RISCIV {
// We use 64 bits as the known part in the scalable vector types.
static constexpr unsigned RVVBitsPerBlock = 64;
} // namespace RISCIV

namespace RISCIVVIntrinsicsTable {

struct RISCIVVIntrinsicInfo {
  unsigned IntrinsicID;
  uint8_t SplatOperand;
};

using namespace RISCIV;

#define GET_RISCIVVIntrinsicsTable_DECL
#include "RISCIVGenSearchableTables.inc"

} // end namespace RISCIVVIntrinsicsTable

} // end namespace llvm

#endif
