//===-- RISCIVRegisterInfo.cpp - RISCIV Register Information ------*- C++ -*-===//
//
// ABI should be ILP32
// wording, remove fp, vector register by harihitode
//
// original license
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains the RISCIV implementation of the TargetRegisterInfo class.
//
//===----------------------------------------------------------------------===//

#include "RISCIVRegisterInfo.h"
#include "RISCIV.h"
#include "RISCIVMachineFunctionInfo.h"
#include "RISCIVSubtarget.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/RegisterScavenging.h"
#include "llvm/CodeGen/TargetFrameLowering.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/Support/ErrorHandling.h"

#define GET_REGINFO_TARGET_DESC
#include "RISCIVGenRegisterInfo.inc"

using namespace llvm;

static_assert(RISCIV::X1 == RISCIV::X0 + 1, "Register list not consecutive");
static_assert(RISCIV::X31 == RISCIV::X0 + 31, "Register list not consecutive");

RISCIVRegisterInfo::RISCIVRegisterInfo(unsigned HwMode)
    : RISCIVGenRegisterInfo(RISCIV::X1, /*DwarfFlavour*/0, /*EHFlavor*/0,
                           /*PC*/0, HwMode) {}

const MCPhysReg *
RISCIVRegisterInfo::getCalleeSavedRegs(const MachineFunction *MF) const {
  auto &Subtarget = MF->getSubtarget<RISCIVSubtarget>();
  if (MF->getFunction().getCallingConv() == CallingConv::GHC)
    return CSR_NoRegs_SaveList;
  if (MF->getFunction().hasFnAttribute("interrupt")) {
    return CSR_Interrupt_SaveList;
  }

  switch (Subtarget.getTargetABI()) {
  default:
    llvm_unreachable("Unrecognized ABI");
  case RISCIVABI::ABI_ILP32:
    return CSR_ILP32_LP64_SaveList;
  }
}

BitVector RISCIVRegisterInfo::getReservedRegs(const MachineFunction &MF) const {
  const RISCIVFrameLowering *TFI = getFrameLowering(MF);
  BitVector Reserved(getNumRegs());

  // Mark any registers requested to be reserved as such
  for (size_t Reg = 0; Reg < getNumRegs(); Reg++) {
    if (MF.getSubtarget<RISCIVSubtarget>().isRegisterReservedByUser(Reg))
      markSuperRegs(Reserved, Reg);
  }

  // Use markSuperRegs to ensure any register aliases are also reserved
  markSuperRegs(Reserved, RISCIV::X0); // zero
  markSuperRegs(Reserved, RISCIV::X2); // sp
  markSuperRegs(Reserved, RISCIV::X3); // gp
  markSuperRegs(Reserved, RISCIV::X4); // tp
  if (TFI->hasFP(MF))
    markSuperRegs(Reserved, RISCIV::X8); // fp
  // Reserve the base register if we need to realign the stack and allocate
  // variable-sized objects at runtime.
  if (TFI->hasBP(MF))
    markSuperRegs(Reserved, RISCIVABI::getBPReg()); // bp

  assert(checkAllSuperRegsMarked(Reserved));
  return Reserved;
}

bool RISCIVRegisterInfo::isAsmClobberable(const MachineFunction &MF,
                                          MCRegister PhysReg) const {
  return !MF.getSubtarget<RISCIVSubtarget>().isRegisterReservedByUser(PhysReg);
}

bool RISCIVRegisterInfo::isConstantPhysReg(MCRegister PhysReg) const {
  return PhysReg == RISCIV::X0;
}

const uint32_t *RISCIVRegisterInfo::getNoPreservedMask() const {
  return CSR_NoRegs_RegMask;
}

// Frame indexes representing locations of CSRs which are given a fixed location
// by save/restore libcalls.
static const std::map<unsigned, int> FixedCSRFIMap = {
  {/*ra*/  RISCIV::X1,   -1},
  {/*s0*/  RISCIV::X8,   -2},
  {/*s1*/  RISCIV::X9,   -3},
  {/*s2*/  RISCIV::X18,  -4},
  {/*s3*/  RISCIV::X19,  -5},
  {/*s4*/  RISCIV::X20,  -6},
  {/*s5*/  RISCIV::X21,  -7},
  {/*s6*/  RISCIV::X22,  -8},
  {/*s7*/  RISCIV::X23,  -9},
  {/*s8*/  RISCIV::X24,  -10},
  {/*s9*/  RISCIV::X25,  -11},
  {/*s10*/ RISCIV::X26,  -12},
  {/*s11*/ RISCIV::X27,  -13}
};

bool RISCIVRegisterInfo::hasReservedSpillSlot(const MachineFunction &MF,
                                              Register Reg,
                                              int &FrameIdx) const {
  const auto *RVFI = MF.getInfo<RISCIVMachineFunctionInfo>();
  if (!RVFI->useSaveRestoreLibCalls(MF))
    return false;

  auto FII = FixedCSRFIMap.find(Reg);
  if (FII == FixedCSRFIMap.end())
    return false;

  FrameIdx = FII->second;
  return true;
}

void RISCIVRegisterInfo::eliminateFrameIndex(MachineBasicBlock::iterator II,
                                             int SPAdj, unsigned FIOperandNum,
                                             RegScavenger *RS) const {
  assert(SPAdj == 0 && "Unexpected non-zero SPAdj value");

  MachineInstr &MI = *II;
  MachineFunction &MF = *MI.getParent()->getParent();
  MachineRegisterInfo &MRI = MF.getRegInfo();
  const RISCIVInstrInfo *TII = MF.getSubtarget<RISCIVSubtarget>().getInstrInfo();
  DebugLoc DL = MI.getDebugLoc();

  int FrameIndex = MI.getOperand(FIOperandNum).getIndex();
  Register FrameReg;
  StackOffset Offset =
      getFrameLowering(MF)->getFrameIndexReference(MF, FrameIndex, FrameReg);

  if (!isInt<32>(Offset.getFixed())) {
    report_fatal_error(
        "Frame offsets outside of the signed 32-bit range not supported");
  }

  MachineBasicBlock &MBB = *MI.getParent();
  bool FrameRegIsKill = false;

  if (!isInt<12>(Offset.getFixed())) {
    // The offset won't fit in an immediate, so use a scratch register instead
    // Modify Offset and FrameReg appropriately
    Register ScratchReg = MRI.createVirtualRegister(&RISCIV::GPRRegClass);
    TII->movImm(MBB, II, DL, ScratchReg, Offset.getFixed());
    if (MI.getOpcode() == RISCIV::ADDI && !Offset.getScalable()) {
      BuildMI(MBB, II, DL, TII->get(RISCIV::ADD), MI.getOperand(0).getReg())
        .addReg(FrameReg)
        .addReg(ScratchReg, RegState::Kill);
      MI.eraseFromParent();
      return;
    }
    BuildMI(MBB, II, DL, TII->get(RISCIV::ADD), ScratchReg)
        .addReg(FrameReg)
        .addReg(ScratchReg, RegState::Kill);
    Offset = StackOffset::get(0, Offset.getScalable());
    FrameReg = ScratchReg;
    FrameRegIsKill = true;
  }

  if (!Offset.getScalable()) {
    // Offset = (fixed offset, 0)
    MI.getOperand(FIOperandNum)
        .ChangeToRegister(FrameReg, false, false, FrameRegIsKill);
    MI.getOperand(FIOperandNum + 1).ChangeToImmediate(Offset.getFixed());
  }
}

Register RISCIVRegisterInfo::getFrameRegister(const MachineFunction &MF) const {
  const TargetFrameLowering *TFI = getFrameLowering(MF);
  return TFI->hasFP(MF) ? RISCIV::X8 : RISCIV::X2;
}

const uint32_t *
RISCIVRegisterInfo::getCallPreservedMask(const MachineFunction & MF,
                                         CallingConv::ID CC) const {
  auto &Subtarget = MF.getSubtarget<RISCIVSubtarget>();

  if (CC == CallingConv::GHC)
    return CSR_NoRegs_RegMask;
  switch (Subtarget.getTargetABI()) {
  default:
    llvm_unreachable("Unrecognized ABI");
  case RISCIVABI::ABI_ILP32:
    return CSR_ILP32_LP64_RegMask;
  }
}

const TargetRegisterClass *
RISCIVRegisterInfo::getLargestLegalSuperClass(const TargetRegisterClass *RC,
                                              const MachineFunction &) const {
  return RC;
}
