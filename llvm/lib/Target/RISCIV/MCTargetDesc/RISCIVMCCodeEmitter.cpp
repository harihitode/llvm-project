//===-- RISCIVMCCodeEmitter.cpp - Convert RISCIV code to machine code -------===//
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
// This file implements the RISCIVMCCodeEmitter class.
//
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/RISCIVBaseInfo.h"
#include "MCTargetDesc/RISCIVFixupKinds.h"
#include "MCTargetDesc/RISCIVMCExpr.h"
#include "MCTargetDesc/RISCIVMCTargetDesc.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCCodeEmitter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCExpr.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCInstBuilder.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/EndianStream.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "mccodeemitter"

STATISTIC(MCNumEmitted, "Number of MC instructions emitted");
STATISTIC(MCNumFixups, "Number of MC fixups created");

namespace {
class RISCIVMCCodeEmitter : public MCCodeEmitter {
  RISCIVMCCodeEmitter(const RISCIVMCCodeEmitter &) = delete;
  void operator=(const RISCIVMCCodeEmitter &) = delete;
  MCContext &Ctx;
  MCInstrInfo const &MCII;

public:
  RISCIVMCCodeEmitter(MCContext &ctx, MCInstrInfo const &MCII)
      : Ctx(ctx), MCII(MCII) {}

  ~RISCIVMCCodeEmitter() override {}

  void encodeInstruction(const MCInst &MI, raw_ostream &OS,
                         SmallVectorImpl<MCFixup> &Fixups,
                         const MCSubtargetInfo &STI) const override;

  void expandFunctionCall(const MCInst &MI, raw_ostream &OS,
                          SmallVectorImpl<MCFixup> &Fixups,
                          const MCSubtargetInfo &STI) const;

  void expandAddTPRel(const MCInst &MI, raw_ostream &OS,
                      SmallVectorImpl<MCFixup> &Fixups,
                      const MCSubtargetInfo &STI) const;

  /// TableGen'erated function for getting the binary encoding for an
  /// instruction.
  uint64_t getBinaryCodeForInstr(const MCInst &MI,
                                 SmallVectorImpl<MCFixup> &Fixups,
                                 const MCSubtargetInfo &STI) const;

  /// Return binary encoding of operand. If the machine operand requires
  /// relocation, record the relocation and return zero.
  unsigned getMachineOpValue(const MCInst &MI, const MCOperand &MO,
                             SmallVectorImpl<MCFixup> &Fixups,
                             const MCSubtargetInfo &STI) const;

  unsigned getImmOpValueAsr1(const MCInst &MI, unsigned OpNo,
                             SmallVectorImpl<MCFixup> &Fixups,
                             const MCSubtargetInfo &STI) const;

  unsigned getImmOpValue(const MCInst &MI, unsigned OpNo,
                         SmallVectorImpl<MCFixup> &Fixups,
                         const MCSubtargetInfo &STI) const;

private:
  FeatureBitset computeAvailableFeatures(const FeatureBitset &FB) const;
  void
  verifyInstructionPredicates(const MCInst &MI,
                              const FeatureBitset &AvailableFeatures) const;
};
} // end anonymous namespace

MCCodeEmitter *llvm::createRISCIVMCCodeEmitter(const MCInstrInfo &MCII,
                                               const MCRegisterInfo &MRI,
                                               MCContext &Ctx) {
  return new RISCIVMCCodeEmitter(Ctx, MCII);
}

// Expand PseudoCALL(Reg), PseudoTAIL and PseudoJump to AUIPC and JALR with
// relocation types. We expand those pseudo-instructions while encoding them,
// meaning AUIPC and JALR won't go through RISCIV MC to MC compressed
// instruction transformation. This is acceptable because AUIPC has no 16-bit
// form and C_JALR has no immediate operand field.  We let linker relaxation
// deal with it. When linker relaxation is enabled, AUIPC and JALR have a
// chance to relax to JAL.
// If the C extension is enabled, JAL has a chance relax to C_JAL.
void RISCIVMCCodeEmitter::expandFunctionCall(const MCInst &MI, raw_ostream &OS,
                                             SmallVectorImpl<MCFixup> &Fixups,
                                             const MCSubtargetInfo &STI) const {
  MCInst TmpInst;
  MCOperand Func;
  MCRegister Ra;
  if (MI.getOpcode() == RISCIV::PseudoTAIL) {
    Func = MI.getOperand(0);
    Ra = RISCIV::X6;
  } else if (MI.getOpcode() == RISCIV::PseudoCALLReg) {
    Func = MI.getOperand(1);
    Ra = MI.getOperand(0).getReg();
  } else if (MI.getOpcode() == RISCIV::PseudoCALL) {
    Func = MI.getOperand(0);
    Ra = RISCIV::X1;
  } else if (MI.getOpcode() == RISCIV::PseudoJump) {
    Func = MI.getOperand(1);
    Ra = MI.getOperand(0).getReg();
  }
  uint32_t Binary;

  assert(Func.isExpr() && "Expected expression");

  const MCExpr *CallExpr = Func.getExpr();

  // Emit AUIPC Ra, Func with R_RISCIV_CALL relocation type.
  TmpInst = MCInstBuilder(RISCIV::AUIPC)
                .addReg(Ra)
                .addOperand(MCOperand::createExpr(CallExpr));
  Binary = getBinaryCodeForInstr(TmpInst, Fixups, STI);
  support::endian::write(OS, Binary, support::little);

  if (MI.getOpcode() == RISCIV::PseudoTAIL ||
      MI.getOpcode() == RISCIV::PseudoJump)
    // Emit JALR X0, Ra, 0
    TmpInst = MCInstBuilder(RISCIV::JALR).addReg(RISCIV::X0).addReg(Ra).addImm(0);
  else
    // Emit JALR Ra, Ra, 0
    TmpInst = MCInstBuilder(RISCIV::JALR).addReg(Ra).addReg(Ra).addImm(0);
  Binary = getBinaryCodeForInstr(TmpInst, Fixups, STI);
  support::endian::write(OS, Binary, support::little);
}

// Expand PseudoAddTPRel to a simple ADD with the correct relocation.
void RISCIVMCCodeEmitter::expandAddTPRel(const MCInst &MI, raw_ostream &OS,
                                         SmallVectorImpl<MCFixup> &Fixups,
                                         const MCSubtargetInfo &STI) const {
  MCOperand DestReg = MI.getOperand(0);
  MCOperand SrcReg = MI.getOperand(1);
  MCOperand TPReg = MI.getOperand(2);
  assert(TPReg.isReg() && TPReg.getReg() == RISCIV::X4 &&
         "Expected thread pointer as second input to TP-relative add");

  MCOperand SrcSymbol = MI.getOperand(3);
  assert(SrcSymbol.isExpr() &&
         "Expected expression as third input to TP-relative add");

  const RISCIVMCExpr *Expr = dyn_cast<RISCIVMCExpr>(SrcSymbol.getExpr());
  assert(Expr && Expr->getKind() == RISCIVMCExpr::VK_RISCIV_TPREL_ADD &&
         "Expected tprel_add relocation on TP-relative symbol");

  // Emit the correct tprel_add relocation for the symbol.
  Fixups.push_back(MCFixup::create(
      0, Expr, MCFixupKind(RISCIV::fixup_risciv_tprel_add), MI.getLoc()));

  // Emit fixup_risciv_relax for tprel_add where the relax feature is enabled.
  if (STI.getFeatureBits()[RISCIV::FeatureRelax]) {
    const MCConstantExpr *Dummy = MCConstantExpr::create(0, Ctx);
    Fixups.push_back(MCFixup::create(
        0, Dummy, MCFixupKind(RISCIV::fixup_risciv_relax), MI.getLoc()));
  }

  // Emit a normal ADD instruction with the given operands.
  MCInst TmpInst = MCInstBuilder(RISCIV::ADD)
                       .addOperand(DestReg)
                       .addOperand(SrcReg)
                       .addOperand(TPReg);
  uint32_t Binary = getBinaryCodeForInstr(TmpInst, Fixups, STI);
  support::endian::write(OS, Binary, support::little);
}

void RISCIVMCCodeEmitter::encodeInstruction(const MCInst &MI, raw_ostream &OS,
                                            SmallVectorImpl<MCFixup> &Fixups,
                                            const MCSubtargetInfo &STI) const {
  verifyInstructionPredicates(MI,
                              computeAvailableFeatures(STI.getFeatureBits()));

  const MCInstrDesc &Desc = MCII.get(MI.getOpcode());
  // Get byte count of instruction.
  unsigned Size = Desc.getSize();

  // RISCIVInstrInfo::getInstSizeInBytes hard-codes the number of expanded
  // instructions for each pseudo, and must be updated when adding new pseudos
  // or changing existing ones.
  if (MI.getOpcode() == RISCIV::PseudoCALLReg ||
      MI.getOpcode() == RISCIV::PseudoCALL ||
      MI.getOpcode() == RISCIV::PseudoTAIL ||
      MI.getOpcode() == RISCIV::PseudoJump) {
    expandFunctionCall(MI, OS, Fixups, STI);
    MCNumEmitted += 2;
    return;
  }

  if (MI.getOpcode() == RISCIV::PseudoAddTPRel) {
    expandAddTPRel(MI, OS, Fixups, STI);
    MCNumEmitted += 1;
    return;
  }

  switch (Size) {
  default:
    llvm_unreachable("Unhandled encodeInstruction length!");
  case 2: {
    uint16_t Bits = getBinaryCodeForInstr(MI, Fixups, STI);
    support::endian::write<uint16_t>(OS, Bits, support::little);
    break;
  }
  case 4: {
    uint32_t Bits = getBinaryCodeForInstr(MI, Fixups, STI);
    support::endian::write(OS, Bits, support::little);
    break;
  }
  }

  ++MCNumEmitted; // Keep track of the # of mi's emitted.
}

unsigned
RISCIVMCCodeEmitter::getMachineOpValue(const MCInst &MI, const MCOperand &MO,
                                       SmallVectorImpl<MCFixup> &Fixups,
                                       const MCSubtargetInfo &STI) const {

  if (MO.isReg())
    return Ctx.getRegisterInfo()->getEncodingValue(MO.getReg());

  if (MO.isImm())
    return static_cast<unsigned>(MO.getImm());

  llvm_unreachable("Unhandled expression!");
  return 0;
}

unsigned
RISCIVMCCodeEmitter::getImmOpValueAsr1(const MCInst &MI, unsigned OpNo,
                                       SmallVectorImpl<MCFixup> &Fixups,
                                       const MCSubtargetInfo &STI) const {
  const MCOperand &MO = MI.getOperand(OpNo);

  if (MO.isImm()) {
    unsigned Res = MO.getImm();
    assert((Res & 1) == 0 && "LSB is non-zero");
    return Res >> 1;
  }

  return getImmOpValue(MI, OpNo, Fixups, STI);
}

unsigned RISCIVMCCodeEmitter::getImmOpValue(const MCInst &MI, unsigned OpNo,
                                           SmallVectorImpl<MCFixup> &Fixups,
                                           const MCSubtargetInfo &STI) const {
  bool EnableRelax = STI.getFeatureBits()[RISCIV::FeatureRelax];
  const MCOperand &MO = MI.getOperand(OpNo);

  MCInstrDesc const &Desc = MCII.get(MI.getOpcode());
  unsigned MIFrm = RISCIVII::getFormat(Desc.TSFlags);

  // If the destination is an immediate, there is nothing to do.
  if (MO.isImm())
    return MO.getImm();

  assert(MO.isExpr() &&
         "getImmOpValue expects only expressions or immediates");
  const MCExpr *Expr = MO.getExpr();
  MCExpr::ExprKind Kind = Expr->getKind();
  RISCIV::Fixups FixupKind = RISCIV::fixup_risciv_invalid;
  bool RelaxCandidate = false;
  if (Kind == MCExpr::Target) {
    const RISCIVMCExpr *RVExpr = cast<RISCIVMCExpr>(Expr);

    switch (RVExpr->getKind()) {
    case RISCIVMCExpr::VK_RISCIV_None:
    case RISCIVMCExpr::VK_RISCIV_Invalid:
    case RISCIVMCExpr::VK_RISCIV_32_PCREL:
      llvm_unreachable("Unhandled fixup kind!");
    case RISCIVMCExpr::VK_RISCIV_TPREL_ADD:
      // tprel_add is only used to indicate that a relocation should be emitted
      // for an add instruction used in TP-relative addressing. It should not be
      // expanded as if representing an actual instruction operand and so to
      // encounter it here is an error.
      llvm_unreachable(
          "VK_RISCIV_TPREL_ADD should not represent an instruction operand");
    case RISCIVMCExpr::VK_RISCIV_LO:
      if (MIFrm == RISCIVII::InstFormatI)
        FixupKind = RISCIV::fixup_risciv_lo12_i;
      else if (MIFrm == RISCIVII::InstFormatS)
        FixupKind = RISCIV::fixup_risciv_lo12_s;
      else
        llvm_unreachable("VK_RISCIV_LO used with unexpected instruction format");
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_HI:
      FixupKind = RISCIV::fixup_risciv_hi20;
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_PCREL_LO:
      if (MIFrm == RISCIVII::InstFormatI)
        FixupKind = RISCIV::fixup_risciv_pcrel_lo12_i;
      else if (MIFrm == RISCIVII::InstFormatS)
        FixupKind = RISCIV::fixup_risciv_pcrel_lo12_s;
      else
        llvm_unreachable(
            "VK_RISCIV_PCREL_LO used with unexpected instruction format");
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_PCREL_HI:
      FixupKind = RISCIV::fixup_risciv_pcrel_hi20;
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_GOT_HI:
      FixupKind = RISCIV::fixup_risciv_got_hi20;
      break;
    case RISCIVMCExpr::VK_RISCIV_TPREL_LO:
      if (MIFrm == RISCIVII::InstFormatI)
        FixupKind = RISCIV::fixup_risciv_tprel_lo12_i;
      else if (MIFrm == RISCIVII::InstFormatS)
        FixupKind = RISCIV::fixup_risciv_tprel_lo12_s;
      else
        llvm_unreachable(
            "VK_RISCIV_TPREL_LO used with unexpected instruction format");
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_TPREL_HI:
      FixupKind = RISCIV::fixup_risciv_tprel_hi20;
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_TLS_GOT_HI:
      FixupKind = RISCIV::fixup_risciv_tls_got_hi20;
      break;
    case RISCIVMCExpr::VK_RISCIV_TLS_GD_HI:
      FixupKind = RISCIV::fixup_risciv_tls_gd_hi20;
      break;
    case RISCIVMCExpr::VK_RISCIV_CALL:
      FixupKind = RISCIV::fixup_risciv_call;
      RelaxCandidate = true;
      break;
    case RISCIVMCExpr::VK_RISCIV_CALL_PLT:
      FixupKind = RISCIV::fixup_risciv_call_plt;
      RelaxCandidate = true;
      break;
    }
  } else if (Kind == MCExpr::SymbolRef &&
             cast<MCSymbolRefExpr>(Expr)->getKind() == MCSymbolRefExpr::VK_None) {
    if (Desc.getOpcode() == RISCIV::JAL) {
      FixupKind = RISCIV::fixup_risciv_jal;
    } else if (MIFrm == RISCIVII::InstFormatB) {
      FixupKind = RISCIV::fixup_risciv_branch;
    } else if (MIFrm == RISCIVII::InstFormatCJ) {
      FixupKind = RISCIV::fixup_risciv_rvc_jump;
    } else if (MIFrm == RISCIVII::InstFormatCB) {
      FixupKind = RISCIV::fixup_risciv_rvc_branch;
    }
  }

  assert(FixupKind != RISCIV::fixup_risciv_invalid && "Unhandled expression!");

  Fixups.push_back(
      MCFixup::create(0, Expr, MCFixupKind(FixupKind), MI.getLoc()));
  ++MCNumFixups;

  // Ensure an R_RISCIV_RELAX relocation will be emitted if linker relaxation is
  // enabled and the current fixup will result in a relocation that may be
  // relaxed.
  if (EnableRelax && RelaxCandidate) {
    const MCConstantExpr *Dummy = MCConstantExpr::create(0, Ctx);
    Fixups.push_back(
    MCFixup::create(0, Dummy, MCFixupKind(RISCIV::fixup_risciv_relax),
                    MI.getLoc()));
    ++MCNumFixups;
  }

  return 0;
}

#define ENABLE_INSTR_PREDICATE_VERIFIER
#include "RISCIVGenMCCodeEmitter.inc"
