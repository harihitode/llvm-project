//===-- RISCIVRegisterInfo.td - RISC-V Register defs -------*- tablegen -*-===//
//
// wording, remove 16/64bit, float, vector registers by harihitode
//
// original license
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
//  Declarations that describe the RISC-V register files
//===----------------------------------------------------------------------===//

let Namespace = "RISCIV" in {
class RISCIVReg<bits<5> Enc, string n, list<string> alt = []> : Register<n> {
  let HWEncoding{4-0} = Enc;
  let AltNames = alt;
}

def ABIRegAltName : RegAltNameIndex;

} // Namespace = "RISCIV"

// Integer registers
// CostPerUse is set higher for registers that may not be compressible as they
// are not part of GPRC, the most restrictive register class used by the
// compressed instruction set. This will influence the greedy register
// allocator to reduce the use of registers that can't be encoded in 16 bit
// instructions. This affects register allocation even when compressed
// instruction isn't targeted, we see no major negative codegen impact.

let RegAltNameIndices = [ABIRegAltName] in {
  def X0  : RISCIVReg<0, "x0", ["zero"]>, DwarfRegNum<[0]>;
  let CostPerUse = [1] in {
  def X1  : RISCIVReg<1, "x1", ["ra"]>, DwarfRegNum<[1]>;
  def X2  : RISCIVReg<2, "x2", ["sp"]>, DwarfRegNum<[2]>;
  def X3  : RISCIVReg<3, "x3", ["gp"]>, DwarfRegNum<[3]>;
  def X4  : RISCIVReg<4, "x4", ["tp"]>, DwarfRegNum<[4]>;
  def X5  : RISCIVReg<5, "x5", ["t0"]>, DwarfRegNum<[5]>;
  def X6  : RISCIVReg<6, "x6", ["t1"]>, DwarfRegNum<[6]>;
  def X7  : RISCIVReg<7, "x7", ["t2"]>, DwarfRegNum<[7]>;
  }
  def X8  : RISCIVReg<8, "x8", ["s0", "fp"]>, DwarfRegNum<[8]>;
  def X9  : RISCIVReg<9, "x9", ["s1"]>, DwarfRegNum<[9]>;
  def X10 : RISCIVReg<10,"x10", ["a0"]>, DwarfRegNum<[10]>;
  def X11 : RISCIVReg<11,"x11", ["a1"]>, DwarfRegNum<[11]>;
  def X12 : RISCIVReg<12,"x12", ["a2"]>, DwarfRegNum<[12]>;
  def X13 : RISCIVReg<13,"x13", ["a3"]>, DwarfRegNum<[13]>;
  def X14 : RISCIVReg<14,"x14", ["a4"]>, DwarfRegNum<[14]>;
  def X15 : RISCIVReg<15,"x15", ["a5"]>, DwarfRegNum<[15]>;
  let CostPerUse = [1] in {
  def X16 : RISCIVReg<16,"x16", ["a6"]>, DwarfRegNum<[16]>;
  def X17 : RISCIVReg<17,"x17", ["a7"]>, DwarfRegNum<[17]>;
  def X18 : RISCIVReg<18,"x18", ["s2"]>, DwarfRegNum<[18]>;
  def X19 : RISCIVReg<19,"x19", ["s3"]>, DwarfRegNum<[19]>;
  def X20 : RISCIVReg<20,"x20", ["s4"]>, DwarfRegNum<[20]>;
  def X21 : RISCIVReg<21,"x21", ["s5"]>, DwarfRegNum<[21]>;
  def X22 : RISCIVReg<22,"x22", ["s6"]>, DwarfRegNum<[22]>;
  def X23 : RISCIVReg<23,"x23", ["s7"]>, DwarfRegNum<[23]>;
  def X24 : RISCIVReg<24,"x24", ["s8"]>, DwarfRegNum<[24]>;
  def X25 : RISCIVReg<25,"x25", ["s9"]>, DwarfRegNum<[25]>;
  def X26 : RISCIVReg<26,"x26", ["s10"]>, DwarfRegNum<[26]>;
  def X27 : RISCIVReg<27,"x27", ["s11"]>, DwarfRegNum<[27]>;
  def X28 : RISCIVReg<28,"x28", ["t3"]>, DwarfRegNum<[28]>;
  def X29 : RISCIVReg<29,"x29", ["t4"]>, DwarfRegNum<[29]>;
  def X30 : RISCIVReg<30,"x30", ["t5"]>, DwarfRegNum<[30]>;
  def X31 : RISCIVReg<31,"x31", ["t6"]>, DwarfRegNum<[31]>;
  }
}

def XLenVT : ValueTypeByHwMode<[RV32], [i32]>;
def XLenRI : RegInfoByHwMode<[RV32], [RegInfo<32,32,32>]>;

// The order of registers represents the preferred allocation sequence.
// Registers are listed in the order caller-save, callee-save, specials.
def GPR : RegisterClass<"RISCIV", [XLenVT], 32, (add
    (sequence "X%u", 10, 17),
    (sequence "X%u", 5, 7),
    (sequence "X%u", 28, 31),
    (sequence "X%u", 8, 9),
    (sequence "X%u", 18, 27),
    (sequence "X%u", 0, 4)
  )> {
  let RegInfos = XLenRI;
}

def GPRX0 : RegisterClass<"RISCIV", [XLenVT], 32, (add X0)> {
  let RegInfos = XLenRI;
}

// The order of registers represents the preferred allocation sequence.
// Registers are listed in the order caller-save, callee-save, specials.
def GPRNoX0 : RegisterClass<"RISCIV", [XLenVT], 32, (add
    (sequence "X%u", 10, 17),
    (sequence "X%u", 5, 7),
    (sequence "X%u", 28, 31),
    (sequence "X%u", 8, 9),
    (sequence "X%u", 18, 27),
    (sequence "X%u", 1, 4)
  )> {
  let RegInfos = XLenRI;
}

def GPRNoX0X2 : RegisterClass<"RISCIV", [XLenVT], 32, (add
    (sequence "X%u", 10, 17),
    (sequence "X%u", 5, 7),
    (sequence "X%u", 28, 31),
    (sequence "X%u", 8, 9),
    (sequence "X%u", 18, 27),
    X1, X3, X4
  )> {
  let RegInfos = XLenRI;
}

// Don't use X1 or X5 for JALR since that is a hint to pop the return address
// stack on some microarchitectures. Also remove the reserved registers X0, X2,
// X3, and X4 as it reduces the number of register classes that get synthesized
// by tablegen.
def GPRJALR : RegisterClass<"RISCIV", [XLenVT], 32, (add
    (sequence "X%u", 10, 17),
    (sequence "X%u", 6, 7),
    (sequence "X%u", 28, 31),
    (sequence "X%u", 8, 9),
    (sequence "X%u", 18, 27)
  )> {
  let RegInfos = XLenRI;
}

def GPRC : RegisterClass<"RISCIV", [XLenVT], 32, (add
    (sequence "X%u", 10, 15),
    (sequence "X%u", 8, 9)
  )> {
  let RegInfos = XLenRI;
}

// For indirect tail calls, we can't use callee-saved registers, as they are
// restored to the saved value before the tail call, which would clobber a call
// address. We shouldn't use x5 since that is a hint for to pop the return
// address stack on some microarchitectures.
def GPRTC : RegisterClass<"RISCIV", [XLenVT], 32, (add
    (sequence "X%u", 6, 7),
    (sequence "X%u", 10, 17),
    (sequence "X%u", 28, 31)
  )> {
  let RegInfos = XLenRI;
}

def SP : RegisterClass<"RISCIV", [XLenVT], 32, (add X2)> {
  let RegInfos = XLenRI;
}
//===----------------------------------------------------------------------===//
// Utility classes for segment load/store.
//===----------------------------------------------------------------------===//
// The set of legal NF for LMUL = lmul.
// LMUL == 1, NF = 2, 3, 4, 5, 6, 7, 8
// LMUL == 2, NF = 2, 3, 4
// LMUL == 4, NF = 2
class NFList<int lmul> {
  list<int> L = !cond(!eq(lmul, 1): [2, 3, 4, 5, 6, 7, 8],
                      !eq(lmul, 2): [2, 3, 4],
                      !eq(lmul, 4): [2],
                      !eq(lmul, 8): []);
}

// Generate [start, end) SubRegIndex list.
class SubRegSet<list<SubRegIndex> LIn, int start, int nf, int lmul> {
  list<SubRegIndex> L = !foldl([]<SubRegIndex>,
                               [0, 1, 2, 3, 4, 5, 6, 7],
                               AccList, i,
                               !listconcat(AccList,
                                 !if(!lt(i, nf),
                                   [!cast<SubRegIndex>("sub_vrm" # lmul # "_" # i)],
                                   [])));
}

class IndexSet<int index, int nf, int lmul> {
  list<int> R =
    !foldl([]<int>,
              [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
               13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
               23, 24, 25, 26, 27, 28, 29, 30, 31],
              L, i,
              !listconcat(L,
                          !if(!and(
                                !le(!mul(index, lmul), !mul(i, lmul)),
                                !le(!mul(i, lmul),
                                    !sub(!add(32, !mul(index, lmul)), !mul(nf, lmul)))
                              ), [!mul(i, lmul)], [])));
}
