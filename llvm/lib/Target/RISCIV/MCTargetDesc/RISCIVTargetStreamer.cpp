//===-- RISCIVTargetStreamer.cpp - RISCIV Target Streamer Methods -----------===//
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
// This file provides RISCIV specific target streamer methods.
//
//===----------------------------------------------------------------------===//

#include "RISCIVTargetStreamer.h"
#include "RISCIVMCTargetDesc.h"
#include "llvm/Support/FormattedStream.h"

using namespace llvm;

RISCIVTargetStreamer::RISCIVTargetStreamer(MCStreamer &S) : MCTargetStreamer(S) {}

void RISCIVTargetStreamer::finish() { finishAttributeSection(); }

void RISCIVTargetStreamer::emitDirectiveOptionPush() {}
void RISCIVTargetStreamer::emitDirectiveOptionPop() {}
void RISCIVTargetStreamer::emitDirectiveOptionPIC() {}
void RISCIVTargetStreamer::emitDirectiveOptionNoPIC() {}
void RISCIVTargetStreamer::emitDirectiveOptionRVC() {}
void RISCIVTargetStreamer::emitDirectiveOptionNoRVC() {}
void RISCIVTargetStreamer::emitDirectiveOptionRelax() {}
void RISCIVTargetStreamer::emitDirectiveOptionNoRelax() {}
void RISCIVTargetStreamer::emitAttribute(unsigned Attribute, unsigned Value) {}
void RISCIVTargetStreamer::finishAttributeSection() {}
void RISCIVTargetStreamer::emitTextAttribute(unsigned Attribute,
                                             StringRef String) {}
void RISCIVTargetStreamer::emitIntTextAttribute(unsigned Attribute,
                                                unsigned IntValue,
                                                StringRef StringValue) {}

void RISCIVTargetStreamer::emitTargetAttributes(const MCSubtargetInfo &STI) {
  return;
}

// This part is for ascii assembly output
RISCIVTargetAsmStreamer::RISCIVTargetAsmStreamer(MCStreamer &S,
                                                 formatted_raw_ostream &OS)
    : RISCIVTargetStreamer(S), OS(OS) {}

void RISCIVTargetAsmStreamer::emitDirectiveOptionPush() {
  OS << "\t.option\tpush\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionPop() {
  OS << "\t.option\tpop\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionPIC() {
  OS << "\t.option\tpic\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionNoPIC() {
  OS << "\t.option\tnopic\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionRVC() {
  OS << "\t.option\trvc\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionNoRVC() {
  OS << "\t.option\tnorvc\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionRelax() {
  OS << "\t.option\trelax\n";
}

void RISCIVTargetAsmStreamer::emitDirectiveOptionNoRelax() {
  OS << "\t.option\tnorelax\n";
}

void RISCIVTargetAsmStreamer::emitAttribute(unsigned Attribute, unsigned Value) {
  OS << "\t.attribute\t" << Attribute << ", " << Twine(Value) << "\n";
}

void RISCIVTargetAsmStreamer::emitTextAttribute(unsigned Attribute,
                                                StringRef String) {
  OS << "\t.attribute\t" << Attribute << ", \"" << String << "\"\n";
}

void RISCIVTargetAsmStreamer::emitIntTextAttribute(unsigned Attribute,
                                                   unsigned IntValue,
                                                   StringRef StringValue) {}

void RISCIVTargetAsmStreamer::finishAttributeSection() {}
