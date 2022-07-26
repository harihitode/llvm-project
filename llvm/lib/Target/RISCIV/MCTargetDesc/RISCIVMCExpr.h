//===-- RISCIVMCExpr.h - RISCIV specific MC expression classes --*- C++ -*-===//
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
// This file describes RISCIV-specific MCExprs, used for modifiers like
// "%hi" or "%lo" etc.,
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_RISCIV_MCTARGETDESC_RISCIVMCEXPR_H
#define LLVM_LIB_TARGET_RISCIV_MCTARGETDESC_RISCIVMCEXPR_H

#include "llvm/MC/MCExpr.h"

namespace llvm {

class StringRef;

class RISCIVMCExpr : public MCTargetExpr {
public:
  enum VariantKind {
    VK_RISCIV_None,
    VK_RISCIV_LO,
    VK_RISCIV_HI,
    VK_RISCIV_PCREL_LO,
    VK_RISCIV_PCREL_HI,
    VK_RISCIV_GOT_HI,
    VK_RISCIV_TPREL_LO,
    VK_RISCIV_TPREL_HI,
    VK_RISCIV_TPREL_ADD,
    VK_RISCIV_TLS_GOT_HI,
    VK_RISCIV_TLS_GD_HI,
    VK_RISCIV_CALL,
    VK_RISCIV_CALL_PLT,
    VK_RISCIV_32_PCREL,
    VK_RISCIV_Invalid // Must be the last item
  };

private:
  const MCExpr *Expr;
  const VariantKind Kind;

  int64_t evaluateAsInt64(int64_t Value) const;

  explicit RISCIVMCExpr(const MCExpr *Expr, VariantKind Kind)
      : Expr(Expr), Kind(Kind) {}

public:
  static const RISCIVMCExpr *create(const MCExpr *Expr, VariantKind Kind,
                                   MCContext &Ctx);

  VariantKind getKind() const { return Kind; }

  const MCExpr *getSubExpr() const { return Expr; }

  /// Get the corresponding PC-relative HI fixup that a VK_RISCIV_PCREL_LO
  /// points to, and optionally the fragment containing it.
  ///
  /// \returns nullptr if this isn't a VK_RISCIV_PCREL_LO pointing to a
  /// known PC-relative HI fixup.
  const MCFixup *getPCRelHiFixup(const MCFragment **DFOut) const;

  void printImpl(raw_ostream &OS, const MCAsmInfo *MAI) const override;
  bool evaluateAsRelocatableImpl(MCValue &Res, const MCAsmLayout *Layout,
                                 const MCFixup *Fixup) const override;
  void visitUsedExpr(MCStreamer &Streamer) const override;
  MCFragment *findAssociatedFragment() const override {
    return getSubExpr()->findAssociatedFragment();
  }

  void fixELFSymbolsInTLSFixups(MCAssembler &Asm) const override;

  bool evaluateAsConstant(int64_t &Res) const;

  static bool classof(const MCExpr *E) {
    return E->getKind() == MCExpr::Target;
  }

  static bool classof(const RISCIVMCExpr *) { return true; }

  static VariantKind getVariantKindForName(StringRef name);
  static StringRef getVariantKindName(VariantKind Kind);
};

} // end namespace llvm.

#endif
