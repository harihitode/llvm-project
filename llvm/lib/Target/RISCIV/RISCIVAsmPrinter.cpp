//===-- RISCIVAsmPrinter.cpp - assembly writer ----------------------------===//
//
// wording and remove compressed instruction by harihitode
//
// original license
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains a printer that converts from our internal representation
// of machine-dependent LLVM code to the assembly language.
//
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/RISCIVInstPrinter.h"
#include "MCTargetDesc/RISCIVMCExpr.h"
#include "MCTargetDesc/RISCIVTargetStreamer.h"
#include "RISCIV.h"
#include "RISCIVTargetMachine.h"
#include "TargetInfo/RISCIVTargetInfo.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/AsmPrinter.h"
#include "llvm/CodeGen/MachineConstantPool.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCStreamer.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

#define DEBUG_TYPE "asm-printer"

namespace {
  class RISCIVAsmPrinter : public AsmPrinter {
    const MCSubtargetInfo *STI;

  public:
    explicit RISCIVAsmPrinter(TargetMachine &TM,
                              std::unique_ptr<MCStreamer> Streamer)
      : AsmPrinter(TM, std::move(Streamer)), STI(TM.getMCSubtargetInfo()) {}

    StringRef getPassName() const override { return "RISCIV Assembly Printer"; }

    bool runOnMachineFunction(MachineFunction &MF) override;

    void emitInstruction(const MachineInstr *MI) override;

    bool PrintAsmOperand(const MachineInstr *MI, unsigned OpNo,
                         const char *ExtraCode, raw_ostream &OS) override;
    bool PrintAsmMemoryOperand(const MachineInstr *MI, unsigned OpNo,
                               const char *ExtraCode, raw_ostream &OS) override;

    bool emitPseudoExpansionLowering(MCStreamer &OutStreamer,
                                     const MachineInstr *MI);

    // Wrapper needed for tblgenned pseudo lowering.
    bool lowerOperand(const MachineOperand &MO, MCOperand &MCOp) const {
      return LowerRISCIVMachineOperandToMCOperand(MO, MCOp, *this);
    }

    void emitStartOfAsmFile(Module &M) override;
    void emitEndOfAsmFile(Module &M) override;

  private:
    void emitAttributes();
  };
}

// Simple pseudo-instructions have their lowering (with expansion to real
// instructions) auto-generated.
#include "RISCIVGenMCPseudoLowering.inc"

void RISCIVAsmPrinter::emitInstruction(const MachineInstr *MI) {
  // Do any auto-generated pseudo lowerings.
  if (emitPseudoExpansionLowering(*OutStreamer, MI))
    return;

  MCInst TmpInst;
  if (!lowerRISCIVMachineInstrToMCInst(MI, TmpInst, *this))
    EmitToStreamer(*OutStreamer, TmpInst);
}

bool RISCIVAsmPrinter::PrintAsmOperand(const MachineInstr *MI, unsigned OpNo,
                                       const char *ExtraCode, raw_ostream &OS) {
  // First try the generic code, which knows about modifiers like 'c' and 'n'.
  if (!AsmPrinter::PrintAsmOperand(MI, OpNo, ExtraCode, OS))
    return false;

  const MachineOperand &MO = MI->getOperand(OpNo);
  if (ExtraCode && ExtraCode[0]) {
    if (ExtraCode[1] != 0)
      return true; // Unknown modifier.

    switch (ExtraCode[0]) {
    default:
      return true; // Unknown modifier.
    case 'z':      // Print zero register if zero, regular printing otherwise.
      if (MO.isImm() && MO.getImm() == 0) {
        OS << RISCIVInstPrinter::getRegisterName(RISCIV::X0);
        return false;
      }
      break;
    case 'i': // Literal 'i' if operand is not a register.
      if (!MO.isReg())
        OS << 'i';
      return false;
    }
  }

  switch (MO.getType()) {
  case MachineOperand::MO_Immediate:
    OS << MO.getImm();
    return false;
  case MachineOperand::MO_Register:
    OS << RISCIVInstPrinter::getRegisterName(MO.getReg());
    return false;
  case MachineOperand::MO_GlobalAddress:
    PrintSymbolOperand(MO, OS);
    return false;
  case MachineOperand::MO_BlockAddress: {
    MCSymbol *Sym = GetBlockAddressSymbol(MO.getBlockAddress());
    Sym->print(OS, MAI);
    return false;
  }
  default:
    break;
  }

  return true;
}

bool RISCIVAsmPrinter::PrintAsmMemoryOperand(const MachineInstr *MI,
                                             unsigned OpNo,
                                             const char *ExtraCode,
                                             raw_ostream &OS) {
  if (!ExtraCode) {
    const MachineOperand &MO = MI->getOperand(OpNo);
    // For now, we only support register memory operands in registers and
    // assume there is no addend
    if (!MO.isReg())
      return true;

    OS << "0(" << RISCIVInstPrinter::getRegisterName(MO.getReg()) << ")";
    return false;
  }

  return AsmPrinter::PrintAsmMemoryOperand(MI, OpNo, ExtraCode, OS);
}

bool RISCIVAsmPrinter::runOnMachineFunction(MachineFunction &MF) {
  // Set the current MCSubtargetInfo to a copy which has the correct
  // feature bits for the current MachineFunction
  MCSubtargetInfo &NewSTI =
    OutStreamer->getContext().getSubtargetCopy(*TM.getMCSubtargetInfo());
  NewSTI.setFeatureBits(MF.getSubtarget().getFeatureBits());
  STI = &NewSTI;

  SetupMachineFunction(MF);
  emitFunctionBody();
  return false;
}

void RISCIVAsmPrinter::emitStartOfAsmFile(Module &M) {
  if (TM.getTargetTriple().isOSBinFormatELF())
    emitAttributes();
}

void RISCIVAsmPrinter::emitEndOfAsmFile(Module &M) {
  RISCIVTargetStreamer &RTS =
    static_cast<RISCIVTargetStreamer &>(*OutStreamer->getTargetStreamer());

  if (TM.getTargetTriple().isOSBinFormatELF())
    RTS.finishAttributeSection();
}

void RISCIVAsmPrinter::emitAttributes() {
  RISCIVTargetStreamer &RTS =
    static_cast<RISCIVTargetStreamer &>(*OutStreamer->getTargetStreamer());
  RTS.emitTargetAttributes(*STI);
}

// Force static initialization.
extern "C" LLVM_EXTERNAL_VISIBILITY void LLVMInitializeRISCIVAsmPrinter() {
  RegisterAsmPrinter<RISCIVAsmPrinter> X(getTheRISCIVTarget());
}
