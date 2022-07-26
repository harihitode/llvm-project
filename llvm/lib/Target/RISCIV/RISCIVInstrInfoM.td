//===-- RISCIVInstrInfoM.td - 'M' instructions -------------*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file describes the RISC-V instructions from the standard 'M', Integer
// Multiplication and Division instruction set extension.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// RISC-V specific DAG Nodes.
//===----------------------------------------------------------------------===//

def risciv_mulhsu : SDNode<"RISCIVISD::MULHSU", SDTIntBinOp>;
def risciv_divw  : SDNode<"RISCIVISD::DIVW",  SDT_RISCIVIntBinOpW>;
def risciv_divuw : SDNode<"RISCIVISD::DIVUW", SDT_RISCIVIntBinOpW>;
def risciv_remuw : SDNode<"RISCIVISD::REMUW", SDT_RISCIVIntBinOpW>;

//===----------------------------------------------------------------------===//
// Instructions
//===----------------------------------------------------------------------===//

let Predicates = [HasStdExtM] in {
def MUL     : ALU_rr<0b0000001, 0b000, "mul">,
              Sched<[WriteIMul, ReadIMul, ReadIMul]>;
def MULH    : ALU_rr<0b0000001, 0b001, "mulh">,
              Sched<[WriteIMul, ReadIMul, ReadIMul]>;
def MULHSU  : ALU_rr<0b0000001, 0b010, "mulhsu">,
              Sched<[WriteIMul, ReadIMul, ReadIMul]>;
def MULHU   : ALU_rr<0b0000001, 0b011, "mulhu">,
              Sched<[WriteIMul, ReadIMul, ReadIMul]>;
def DIV     : ALU_rr<0b0000001, 0b100, "div">,
              Sched<[WriteIDiv, ReadIDiv, ReadIDiv]>;
def DIVU    : ALU_rr<0b0000001, 0b101, "divu">,
              Sched<[WriteIDiv, ReadIDiv, ReadIDiv]>;
def REM     : ALU_rr<0b0000001, 0b110, "rem">,
              Sched<[WriteIDiv, ReadIDiv, ReadIDiv]>;
def REMU    : ALU_rr<0b0000001, 0b111, "remu">,
              Sched<[WriteIDiv, ReadIDiv, ReadIDiv]>;
} // Predicates = [HasStdExtM]

//===----------------------------------------------------------------------===//
// Pseudo-instructions and codegen patterns
//===----------------------------------------------------------------------===//

let Predicates = [HasStdExtM] in {
def : PatGprGpr<mul, MUL>;
def : PatGprGpr<mulhs, MULH>;
def : PatGprGpr<mulhu, MULHU>;
def : PatGprGpr<risciv_mulhsu, MULHSU>;
def : PatGprGpr<sdiv, DIV>;
def : PatGprGpr<udiv, DIVU>;
def : PatGprGpr<srem, REM>;
def : PatGprGpr<urem, REMU>;
} // Predicates = [HasStdExtM]
