//===-- RISCIVRegisterInfo.h - Register Information Impl --------*- C++ -*-===//
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
// This file contains the RISCIV implementation of the TargetRegisterInfo class.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_RISCIV_RISCIVREGISTERINFO_H
#define LLVM_LIB_TARGET_RISCIV_RISCIVREGISTERINFO_H

#include "llvm/CodeGen/TargetRegisterInfo.h"

#define GET_REGINFO_HEADER
#include "RISCIVGenRegisterInfo.inc"

namespace llvm {

struct RISCIVRegisterInfo : public RISCIVGenRegisterInfo {

  RISCIVRegisterInfo(unsigned HwMode);

  const uint32_t *getCallPreservedMask(const MachineFunction &MF,
                                       CallingConv::ID) const override;

  const MCPhysReg *getCalleeSavedRegs(const MachineFunction *MF) const override;

  BitVector getReservedRegs(const MachineFunction &MF) const override;
  bool isAsmClobberable(const MachineFunction &MF,
                        MCRegister PhysReg) const override;

  bool isConstantPhysReg(MCRegister PhysReg) const override;

  const uint32_t *getNoPreservedMask() const override;

  bool hasReservedSpillSlot(const MachineFunction &MF, Register Reg,
                            int &FrameIdx) const override;

  void eliminateFrameIndex(MachineBasicBlock::iterator MI, int SPAdj,
                           unsigned FIOperandNum,
                           RegScavenger *RS = nullptr) const override;

  Register getFrameRegister(const MachineFunction &MF) const override;

  bool requiresRegisterScavenging(const MachineFunction &MF) const override {
    return true;
  }

  bool requiresFrameIndexScavenging(const MachineFunction &MF) const override {
    return true;
  }

  const TargetRegisterClass *
  getPointerRegClass(const MachineFunction &MF,
                     unsigned Kind = 0) const override {
    return &RISCIV::GPRRegClass;
  }

  const TargetRegisterClass *
  getLargestLegalSuperClass(const TargetRegisterClass *RC,
                            const MachineFunction &) const override;
};
}

#endif
