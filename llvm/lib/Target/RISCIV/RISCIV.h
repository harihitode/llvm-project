//===-- RISCIV.h - Top-level interface for RISCIV ---------------*- C++ -*-===//
//
// Naming Change by harihitode
//
// Original License
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_RISCIV_RISCIV_H
#define LLVM_LIB_TARGET_RISCIV_RISCIV_H

#include "MCTargetDesc/RISCIVBaseInfo.h"
#include "llvm/Target/TargetMachine.h"

namespace llvm {
class RISCIVRegisterBankInfo;
class RISCIVSubtarget;
class RISCIVTargetMachine;
class AsmPrinter;
class FunctionPass;
class InstructionSelector;
class MCInst;
class MCOperand;
class MachineInstr;
class MachineOperand;
class PassRegistry;

bool lowerRISCIVMachineInstrToMCInst(const MachineInstr *MI, MCInst &OutMI,
                                     AsmPrinter &AP);
bool LowerRISCIVMachineOperandToMCOperand(const MachineOperand &MO,
                                          MCOperand &MCOp, const AsmPrinter &AP);

FunctionPass *createRISCIVISelDag(RISCIVTargetMachine &TM);

FunctionPass *createRISCIVMergeBaseOffsetOptPass();
void initializeRISCIVMergeBaseOffsetOptPass(PassRegistry &);

FunctionPass *createRISCIVExpandPseudoPass();
void initializeRISCIVExpandPseudoPass(PassRegistry &);

FunctionPass *createRISCIVExpandAtomicPseudoPass();
void initializeRISCIVExpandAtomicPseudoPass(PassRegistry &);

FunctionPass *createRISCIVInsertVSETVLIPass();
void initializeRISCIVInsertVSETVLIPass(PassRegistry &);

InstructionSelector *createRISCIVInstructionSelector(const RISCIVTargetMachine &,
                                                     RISCIVSubtarget &,
                                                     RISCIVRegisterBankInfo &);
}

#endif
