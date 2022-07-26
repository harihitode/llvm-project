//===-- RISCIVMCInstLower.cpp - Convert RISCIV MachineInstr to an MCInst ----=//
//
// remove vector machine inst lowering, wording by harihitode
//
// original license
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains code to lower RISCIV MachineInstrs to their corresponding
// MCInst records.
//
//===----------------------------------------------------------------------===//

#include "RISCIV.h"
#include "RISCIVSubtarget.h"
#include "MCTargetDesc/RISCIVMCExpr.h"
#include "llvm/CodeGen/AsmPrinter.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCExpr.h"
#include "llvm/MC/MCInst.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static MCOperand lowerSymbolOperand(const MachineOperand &MO, MCSymbol *Sym,
                                    const AsmPrinter &AP) {
  MCContext &Ctx = AP.OutContext;
  RISCIVMCExpr::VariantKind Kind;

  switch (MO.getTargetFlags()) {
  default:
    llvm_unreachable("Unknown target flag on GV operand");
  case RISCIVII::MO_None:
    Kind = RISCIVMCExpr::VK_RISCIV_None;
    break;
  case RISCIVII::MO_CALL:
    Kind = RISCIVMCExpr::VK_RISCIV_CALL;
    break;
  case RISCIVII::MO_PLT:
    Kind = RISCIVMCExpr::VK_RISCIV_CALL_PLT;
    break;
  case RISCIVII::MO_LO:
    Kind = RISCIVMCExpr::VK_RISCIV_LO;
    break;
  case RISCIVII::MO_HI:
    Kind = RISCIVMCExpr::VK_RISCIV_HI;
    break;
  case RISCIVII::MO_PCREL_LO:
    Kind = RISCIVMCExpr::VK_RISCIV_PCREL_LO;
    break;
  case RISCIVII::MO_PCREL_HI:
    Kind = RISCIVMCExpr::VK_RISCIV_PCREL_HI;
    break;
  case RISCIVII::MO_GOT_HI:
    Kind = RISCIVMCExpr::VK_RISCIV_GOT_HI;
    break;
  case RISCIVII::MO_TPREL_LO:
    Kind = RISCIVMCExpr::VK_RISCIV_TPREL_LO;
    break;
  case RISCIVII::MO_TPREL_HI:
    Kind = RISCIVMCExpr::VK_RISCIV_TPREL_HI;
    break;
  case RISCIVII::MO_TPREL_ADD:
    Kind = RISCIVMCExpr::VK_RISCIV_TPREL_ADD;
    break;
  case RISCIVII::MO_TLS_GOT_HI:
    Kind = RISCIVMCExpr::VK_RISCIV_TLS_GOT_HI;
    break;
  case RISCIVII::MO_TLS_GD_HI:
    Kind = RISCIVMCExpr::VK_RISCIV_TLS_GD_HI;
    break;
  }

  const MCExpr *ME =
      MCSymbolRefExpr::create(Sym, MCSymbolRefExpr::VK_None, Ctx);

  if (!MO.isJTI() && !MO.isMBB() && MO.getOffset())
    ME = MCBinaryExpr::createAdd(
        ME, MCConstantExpr::create(MO.getOffset(), Ctx), Ctx);

  if (Kind != RISCIVMCExpr::VK_RISCIV_None)
    ME = RISCIVMCExpr::create(ME, Kind, Ctx);
  return MCOperand::createExpr(ME);
}

bool llvm::LowerRISCIVMachineOperandToMCOperand(const MachineOperand &MO,
                                               MCOperand &MCOp,
                                               const AsmPrinter &AP) {
  switch (MO.getType()) {
  default:
    report_fatal_error("LowerRISCIVMachineInstrToMCInst: unknown operand type");
  case MachineOperand::MO_Register:
    // Ignore all implicit register operands.
    if (MO.isImplicit())
      return false;
    MCOp = MCOperand::createReg(MO.getReg());
    break;
  case MachineOperand::MO_RegisterMask:
    // Regmasks are like implicit defs.
    return false;
  case MachineOperand::MO_Immediate:
    MCOp = MCOperand::createImm(MO.getImm());
    break;
  case MachineOperand::MO_MachineBasicBlock:
    MCOp = lowerSymbolOperand(MO, MO.getMBB()->getSymbol(), AP);
    break;
  case MachineOperand::MO_GlobalAddress:
    MCOp = lowerSymbolOperand(MO, AP.getSymbolPreferLocal(*MO.getGlobal()), AP);
    break;
  case MachineOperand::MO_BlockAddress:
    MCOp = lowerSymbolOperand(
                              MO, AP.GetBlockAddressSymbol(MO.getBlockAddress()), AP);
    break;
  case MachineOperand::MO_ExternalSymbol:
    MCOp = lowerSymbolOperand(
                              MO, AP.GetExternalSymbolSymbol(MO.getSymbolName()), AP);
    break;
  case MachineOperand::MO_ConstantPoolIndex:
    MCOp = lowerSymbolOperand(MO, AP.GetCPISymbol(MO.getIndex()), AP);
    break;
  case MachineOperand::MO_JumpTableIndex:
    MCOp = lowerSymbolOperand(MO, AP.GetJTISymbol(MO.getIndex()), AP);
    break;
  }
  return true;
}

bool llvm::lowerRISCIVMachineInstrToMCInst(const MachineInstr *MI, MCInst &OutMI,
                                          AsmPrinter &AP) {
  OutMI.setOpcode(MI->getOpcode());

  for (const MachineOperand &MO : MI->operands()) {
    MCOperand MCOp;
    if (LowerRISCIVMachineOperandToMCOperand(MO, MCOp, AP))
      OutMI.addOperand(MCOp);
  }
  return false;
}
