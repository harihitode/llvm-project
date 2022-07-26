//===-- RISCIVSubtarget.cpp - RISCIV Subtarget Information ----------------===//
//
// remove subtargets by harihitode
//
// original license
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the RISCIV specific subclass of TargetSubtargetInfo.
//
//===----------------------------------------------------------------------===//

#include "RISCIVSubtarget.h"
#include "RISCIV.h"
#include "RISCIVCallLowering.h"
#include "RISCIVFrameLowering.h"
#include "RISCIVLegalizerInfo.h"
#include "RISCIVRegisterBankInfo.h"
#include "RISCIVTargetMachine.h"
#include "llvm/Support/TargetRegistry.h"

using namespace llvm;

#define DEBUG_TYPE "risciv-subtarget"

#define GET_SUBTARGETINFO_TARGET_DESC
#define GET_SUBTARGETINFO_CTOR
#include "RISCIVGenSubtargetInfo.inc"

void RISCIVSubtarget::anchor() {}

RISCIVSubtarget &
RISCIVSubtarget::initializeSubtargetDependencies(const Triple &TT, StringRef CPU,
                                                StringRef TuneCPU, StringRef FS,
                                                StringRef ABIName) {
  // Determine default and user-specified characteristics
  bool Is64Bit = TT.isArch64Bit();
  if (CPU.empty())
    CPU = Is64Bit ? "generic-rv64" : "generic-rv32";
  if (CPU == "generic")
    report_fatal_error(Twine("CPU 'generic' is not supported. Use ") +
                       (Is64Bit ? "generic-rv64" : "generic-rv32"));

  if (TuneCPU.empty())
    TuneCPU = CPU;

  ParseSubtargetFeatures(CPU, TuneCPU, FS);
  if (Is64Bit) {
    XLenVT = MVT::i64;
    XLen = 64;
  }

  TargetABI = RISCIVABI::computeTargetABI(TT, getFeatureBits(), ABIName);
  RISCIVFeatures::validate(TT, getFeatureBits());
  return *this;
}

RISCIVSubtarget::RISCIVSubtarget(const Triple &TT, StringRef CPU,
                               StringRef TuneCPU, StringRef FS,
                               StringRef ABIName, const TargetMachine &TM)
    : RISCIVGenSubtargetInfo(TT, CPU, TuneCPU, FS),
      UserReservedRegister(RISCIV::NUM_TARGET_REGS),
      FrameLowering(initializeSubtargetDependencies(TT, CPU, TuneCPU, FS, ABIName)),
      InstrInfo(*this), RegInfo(getHwMode()), TLInfo(TM, *this) {
  CallLoweringInfo.reset(new RISCIVCallLowering(*getTargetLowering()));
  Legalizer.reset(new RISCIVLegalizerInfo(*this));

  auto *RBI = new RISCIVRegisterBankInfo(*getRegisterInfo());
  RegBankInfo.reset(RBI);
  InstSelector.reset(createRISCIVInstructionSelector(
      *static_cast<const RISCIVTargetMachine *>(&TM), *this, *RBI));
}

const CallLowering *RISCIVSubtarget::getCallLowering() const {
  return CallLoweringInfo.get();
}

InstructionSelector *RISCIVSubtarget::getInstructionSelector() const {
  return InstSelector.get();
}

const LegalizerInfo *RISCIVSubtarget::getLegalizerInfo() const {
  return Legalizer.get();
}

const RegisterBankInfo *RISCIVSubtarget::getRegBankInfo() const {
  return RegBankInfo.get();
}
