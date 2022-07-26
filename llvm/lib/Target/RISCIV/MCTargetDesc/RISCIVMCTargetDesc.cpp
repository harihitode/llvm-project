//===-- RISCIVMCTargetDesc.cpp - RISCIV Target Descriptions -----------------===//
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
///
/// This file provides RISCIV-specific target descriptions.
///
//===----------------------------------------------------------------------===//

#include "RISCIVMCTargetDesc.h"
#include "RISCIVBaseInfo.h"
#include "RISCIVELFStreamer.h"
#include "RISCIVInstPrinter.h"
#include "RISCIVMCAsmInfo.h"
#include "RISCIVTargetStreamer.h"
#include "TargetInfo/RISCIVTargetInfo.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/MC/MCAsmBackend.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCCodeEmitter.h"
#include "llvm/MC/MCInstrAnalysis.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCObjectWriter.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/TargetRegistry.h"

#define GET_INSTRINFO_MC_DESC
#include "RISCIVGenInstrInfo.inc"

#define GET_REGINFO_MC_DESC
#include "RISCIVGenRegisterInfo.inc"

#define GET_SUBTARGETINFO_MC_DESC
#include "RISCIVGenSubtargetInfo.inc"

using namespace llvm;

static MCInstrInfo *createRISCIVMCInstrInfo() {
  MCInstrInfo *X = new MCInstrInfo();
  InitRISCIVMCInstrInfo(X);
  return X;
}

static MCRegisterInfo *createRISCIVMCRegisterInfo(const Triple &TT) {
  MCRegisterInfo *X = new MCRegisterInfo();
  InitRISCIVMCRegisterInfo(X, RISCIV::X1);
  return X;
}

static MCAsmInfo *createRISCIVMCAsmInfo(const MCRegisterInfo &MRI,
                                        const Triple &TT,
                                        const MCTargetOptions &Options) {
  MCAsmInfo *MAI = new RISCIVMCAsmInfo(TT);

  MCRegister SP = MRI.getDwarfRegNum(RISCIV::X2, true);
  MCCFIInstruction Inst = MCCFIInstruction::cfiDefCfa(nullptr, SP, 0);
  MAI->addInitialFrameState(Inst);

  return MAI;
}

static MCSubtargetInfo *createRISCIVMCSubtargetInfo(const Triple &TT,
                                                    StringRef CPU, StringRef FS) {
  if (CPU.empty())
    CPU = TT.isArch64Bit() ? "generic-rv64" : "generic-rv32";
  if (CPU == "generic")
    report_fatal_error(Twine("CPU 'generic' is not supported. Use ") +
                       (TT.isArch64Bit() ? "generic-rv64" : "generic-rv32"));
  return createRISCIVMCSubtargetInfoImpl(TT, CPU, /*TuneCPU*/ CPU, FS);
}

static MCInstPrinter *createRISCIVMCInstPrinter(const Triple &T,
                                                unsigned SyntaxVariant,
                                                const MCAsmInfo &MAI,
                                                const MCInstrInfo &MII,
                                                const MCRegisterInfo &MRI) {
  return new RISCIVInstPrinter(MAI, MII, MRI);
}

static MCTargetStreamer *
createRISCIVObjectTargetStreamer(MCStreamer &S, const MCSubtargetInfo &STI) {
  const Triple &TT = STI.getTargetTriple();
  if (TT.isOSBinFormatELF())
    return new RISCIVTargetELFStreamer(S, STI);
  return nullptr;
}

static MCTargetStreamer *createRISCIVAsmTargetStreamer(MCStreamer &S,
                                                       formatted_raw_ostream &OS,
                                                       MCInstPrinter *InstPrint,
                                                       bool isVerboseAsm) {
  return new RISCIVTargetAsmStreamer(S, OS);
}

static MCTargetStreamer *createRISCIVNullTargetStreamer(MCStreamer &S) {
  return new RISCIVTargetStreamer(S);
}

namespace {

class RISCIVMCInstrAnalysis : public MCInstrAnalysis {
public:
  explicit RISCIVMCInstrAnalysis(const MCInstrInfo *Info)
      : MCInstrAnalysis(Info) {}

  bool evaluateBranch(const MCInst &Inst, uint64_t Addr, uint64_t Size,
                      uint64_t &Target) const override {
    if (isConditionalBranch(Inst)) {
      int64_t Imm;
      if (Size == 2)
        Imm = Inst.getOperand(1).getImm();
      else
        Imm = Inst.getOperand(2).getImm();
      Target = Addr + Imm;
      return true;
    }

    if (Inst.getOpcode() == RISCIV::JAL) {
      Target = Addr + Inst.getOperand(1).getImm();
      return true;
    }

    return false;
  }
};

} // end anonymous namespace

static MCInstrAnalysis *createRISCIVInstrAnalysis(const MCInstrInfo *Info) {
  return new RISCIVMCInstrAnalysis(Info);
}

namespace {
MCStreamer *createRISCIVELFStreamer(const Triple &T, MCContext &Context,
                                    std::unique_ptr<MCAsmBackend> &&MAB,
                                    std::unique_ptr<MCObjectWriter> &&MOW,
                                    std::unique_ptr<MCCodeEmitter> &&MCE,
                                    bool RelaxAll) {
  return createRISCIVELFStreamer(Context, std::move(MAB), std::move(MOW),
                                 std::move(MCE), RelaxAll);
}
} // end anonymous namespace

extern "C" LLVM_EXTERNAL_VISIBILITY void LLVMInitializeRISCIVTargetMC() {
  Target *T = &getTheRISCIVTarget();
  TargetRegistry::RegisterMCAsmInfo(*T, createRISCIVMCAsmInfo);
  TargetRegistry::RegisterMCInstrInfo(*T, createRISCIVMCInstrInfo);
  TargetRegistry::RegisterMCRegInfo(*T, createRISCIVMCRegisterInfo);
  TargetRegistry::RegisterMCAsmBackend(*T, createRISCIVAsmBackend);
  TargetRegistry::RegisterMCCodeEmitter(*T, createRISCIVMCCodeEmitter);
  TargetRegistry::RegisterMCInstPrinter(*T, createRISCIVMCInstPrinter);
  TargetRegistry::RegisterMCSubtargetInfo(*T, createRISCIVMCSubtargetInfo);
  TargetRegistry::RegisterELFStreamer(*T, createRISCIVELFStreamer);
  TargetRegistry::RegisterObjectTargetStreamer(*T, createRISCIVObjectTargetStreamer);
  TargetRegistry::RegisterMCInstrAnalysis(*T, createRISCIVInstrAnalysis);

  // Register the asm target streamer.
  TargetRegistry::RegisterAsmTargetStreamer(*T, createRISCIVAsmTargetStreamer);
  // Register the null target streamer.
  TargetRegistry::RegisterNullTargetStreamer(*T,
                                             createRISCIVNullTargetStreamer);
}
