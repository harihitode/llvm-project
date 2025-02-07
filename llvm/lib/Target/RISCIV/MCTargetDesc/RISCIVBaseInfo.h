//===-- RISCIVBaseInfo.h - Top level definitions for MC ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains small standalone enum definitions for the RISCIV target
// useful for the compiler back-end and the MC libraries.
//
//===----------------------------------------------------------------------===//
#ifndef LLVM_LIB_TARGET_RISCIV_MCTARGETDESC_RISCIVBASEINFO_H
#define LLVM_LIB_TARGET_RISCIV_MCTARGETDESC_RISCIVBASEINFO_H

#include "MCTargetDesc/RISCIVMCTargetDesc.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/MC/MCInstrDesc.h"
#include "llvm/MC/SubtargetFeature.h"

namespace llvm {

// RISCIVII - This namespace holds all of the target specific flags that
// instruction info tracks. All definitions must match RISCIVInstrFormats.td.
namespace RISCIVII {
enum {
  InstFormatPseudo = 0,
  InstFormatR = 1,
  InstFormatR4 = 2,
  InstFormatI = 3,
  InstFormatS = 4,
  InstFormatB = 5,
  InstFormatU = 6,
  InstFormatJ = 7,
  InstFormatCR = 8,
  InstFormatCI = 9,
  InstFormatCSS = 10,
  InstFormatCIW = 11,
  InstFormatCL = 12,
  InstFormatCS = 13,
  InstFormatCA = 14,
  InstFormatCB = 15,
  InstFormatCJ = 16,
  InstFormatOther = 17,

  InstFormatMask = 31,
  InstFormatShift = 0,

  ConstraintShift = InstFormatShift + 5,
  ConstraintMask = 0b111 << ConstraintShift,

  VLMulShift = ConstraintShift + 3,
  VLMulMask = 0b111 << VLMulShift,

  // Do we need to add a dummy mask op when converting RVV Pseudo to MCInst.
  HasDummyMaskOpShift = VLMulShift + 3,
  HasDummyMaskOpMask = 1 << HasDummyMaskOpShift,

  // Force a tail agnostic policy even this instruction has a tied destination.
  ForceTailAgnosticShift = HasDummyMaskOpShift + 1,
  ForceTailAgnosticMask = 1 << ForceTailAgnosticShift,

  // Does this instruction have a merge operand that must be removed when
  // converting to MCInst. It will be the first explicit use operand. Used by
  // RVV Pseudos.
  HasMergeOpShift = ForceTailAgnosticShift + 1,
  HasMergeOpMask = 1 << HasMergeOpShift,

  // Does this instruction have a SEW operand. It will be the last explicit
  // operand. Used by RVV Pseudos.
  HasSEWOpShift = HasMergeOpShift + 1,
  HasSEWOpMask = 1 << HasSEWOpShift,

  // Does this instruction have a VL operand. It will be the second to last
  // explicit operand. Used by RVV Pseudos.
  HasVLOpShift = HasSEWOpShift + 1,
  HasVLOpMask = 1 << HasVLOpShift,
};

// Match with the definitions in RISCIVInstrFormatsV.td
enum VConstraintType {
  NoConstraint = 0,
  VS2Constraint = 0b001,
  VS1Constraint = 0b010,
  VMConstraint = 0b100,
};

enum VLMUL : uint8_t {
  LMUL_1 = 0,
  LMUL_2,
  LMUL_4,
  LMUL_8,
  LMUL_RESERVED,
  LMUL_F8,
  LMUL_F4,
  LMUL_F2
};

// Helper functions to read TSFlags.
/// \returns the format of the instruction.
static inline unsigned getFormat(uint64_t TSFlags) {
  return (TSFlags & InstFormatMask) >> InstFormatShift;
}
/// \returns the constraint for the instruction.
static inline VConstraintType getConstraint(uint64_t TSFlags) {
  return static_cast<VConstraintType>
             ((TSFlags & ConstraintMask) >> ConstraintShift);
}
/// \returns the LMUL for the instruction.
static inline VLMUL getLMul(uint64_t TSFlags) {
  return static_cast<VLMUL>((TSFlags & VLMulMask) >> VLMulShift);
}
/// \returns true if there is a dummy mask operand for the instruction.
static inline bool hasDummyMaskOp(uint64_t TSFlags) {
  return TSFlags & HasDummyMaskOpMask;
}
/// \returns true if tail agnostic is enforced for the instruction.
static inline bool doesForceTailAgnostic(uint64_t TSFlags) {
  return TSFlags & ForceTailAgnosticMask;
}
/// \returns true if there is a merge operand for the instruction.
static inline bool hasMergeOp(uint64_t TSFlags) {
  return TSFlags & HasMergeOpMask;
}
/// \returns true if there is a SEW operand for the instruction.
static inline bool hasSEWOp(uint64_t TSFlags) {
  return TSFlags & HasSEWOpMask;
}
/// \returns true if there is a VL operand for the instruction.
static inline bool hasVLOp(uint64_t TSFlags) {
  return TSFlags & HasVLOpMask;
}

// RISC-V Specific Machine Operand Flags
enum {
  MO_None = 0,
  MO_CALL = 1,
  MO_PLT = 2,
  MO_LO = 3,
  MO_HI = 4,
  MO_PCREL_LO = 5,
  MO_PCREL_HI = 6,
  MO_GOT_HI = 7,
  MO_TPREL_LO = 8,
  MO_TPREL_HI = 9,
  MO_TPREL_ADD = 10,
  MO_TLS_GOT_HI = 11,
  MO_TLS_GD_HI = 12,

  // Used to differentiate between target-specific "direct" flags and "bitmask"
  // flags. A machine operand can only have one "direct" flag, but can have
  // multiple "bitmask" flags.
  MO_DIRECT_FLAG_MASK = 15
};
} // namespace RISCIVII

namespace RISCIVOp {
enum OperandType : unsigned {
  OPERAND_FIRST_RISCIV_IMM = MCOI::OPERAND_FIRST_TARGET,
  OPERAND_UIMM4 = OPERAND_FIRST_RISCIV_IMM,
  OPERAND_UIMM5,
  OPERAND_UIMM12,
  OPERAND_SIMM12,
  OPERAND_UIMM20,
  OPERAND_UIMMLOG2XLEN,
  OPERAND_LAST_RISCIV_IMM = OPERAND_UIMMLOG2XLEN,
  // Operand is either a register or uimm5, this is used by V extension pseudo
  // instructions to represent a value that be passed as AVL to either vsetvli
  // or vsetivli.
  OPERAND_AVL,
};
} // namespace RISCIVOp

// Describes the predecessor/successor bits used in the FENCE instruction.
namespace RISCIVFenceField {
enum FenceField {
  I = 8,
  O = 4,
  R = 2,
  W = 1
};
}

// Describes the supported floating point rounding mode encodings.
namespace RISCIVFPRndMode {
enum RoundingMode {
  RNE = 0,
  RTZ = 1,
  RDN = 2,
  RUP = 3,
  RMM = 4,
  DYN = 7,
  Invalid
};

inline static StringRef roundingModeToString(RoundingMode RndMode) {
  switch (RndMode) {
  default:
    llvm_unreachable("Unknown floating point rounding mode");
  case RISCIVFPRndMode::RNE:
    return "rne";
  case RISCIVFPRndMode::RTZ:
    return "rtz";
  case RISCIVFPRndMode::RDN:
    return "rdn";
  case RISCIVFPRndMode::RUP:
    return "rup";
  case RISCIVFPRndMode::RMM:
    return "rmm";
  case RISCIVFPRndMode::DYN:
    return "dyn";
  }
}

inline static RoundingMode stringToRoundingMode(StringRef Str) {
  return StringSwitch<RoundingMode>(Str)
      .Case("rne", RISCIVFPRndMode::RNE)
      .Case("rtz", RISCIVFPRndMode::RTZ)
      .Case("rdn", RISCIVFPRndMode::RDN)
      .Case("rup", RISCIVFPRndMode::RUP)
      .Case("rmm", RISCIVFPRndMode::RMM)
      .Case("dyn", RISCIVFPRndMode::DYN)
      .Default(RISCIVFPRndMode::Invalid);
}

inline static bool isValidRoundingMode(unsigned Mode) {
  switch (Mode) {
  default:
    return false;
  case RISCIVFPRndMode::RNE:
  case RISCIVFPRndMode::RTZ:
  case RISCIVFPRndMode::RDN:
  case RISCIVFPRndMode::RUP:
  case RISCIVFPRndMode::RMM:
  case RISCIVFPRndMode::DYN:
    return true;
  }
}
} // namespace RISCIVFPRndMode

namespace RISCIVSysReg {
struct SysReg {
  const char *Name;
  const char *AltName;
  const char *DeprecatedName;
  unsigned Encoding;
  // FIXME: add these additional fields when needed.
  // Privilege Access: Read, Write, Read-Only.
  // unsigned ReadWrite;
  // Privilege Mode: User, System or Machine.
  // unsigned Mode;
  // Check field name.
  // unsigned Extra;
  // Register number without the privilege bits.
  // unsigned Number;
  FeatureBitset FeaturesRequired;
  bool isRV32Only;

  bool haveRequiredFeatures(const FeatureBitset &ActiveFeatures) const {
    // Not in 32-bit mode.
    if (isRV32Only && ActiveFeatures[RISCIV::Feature64Bit])
      return false;
    // No required feature associated with the system register.
    if (FeaturesRequired.none())
      return true;
    return (FeaturesRequired & ActiveFeatures) == FeaturesRequired;
  }
};

#define GET_SysRegsList_DECL
#include "RISCIVGenSearchableTables.inc"
} // end namespace RISCIVSysReg

namespace RISCIVABI {

enum ABI {
  ABI_ILP32,
  ABI_ILP32F,
  ABI_ILP32D,
  ABI_ILP32E,
  ABI_LP64,
  ABI_LP64F,
  ABI_LP64D,
  ABI_Unknown
};

// Returns the target ABI, or else a StringError if the requested ABIName is
// not supported for the given TT and FeatureBits combination.
ABI computeTargetABI(const Triple &TT, FeatureBitset FeatureBits,
                     StringRef ABIName);

ABI getTargetABI(StringRef ABIName);

// Returns the register used to hold the stack pointer after realignment.
MCRegister getBPReg();

// Returns the register holding shadow call stack pointer.
MCRegister getSCSPReg();

} // namespace RISCIVABI

namespace RISCIVFeatures {

// Validates if the given combination of features are valid for the target
// triple. Exits with report_fatal_error if not.
void validate(const Triple &TT, const FeatureBitset &FeatureBits);

} // namespace RISCIVFeatures

namespace RISCIVVType {
// Is this a SEW value that can be encoded into the VTYPE format.
inline static bool isValidSEW(unsigned SEW) {
  return isPowerOf2_32(SEW) && SEW >= 8 && SEW <= 1024;
}

// Is this a LMUL value that can be encoded into the VTYPE format.
inline static bool isValidLMUL(unsigned LMUL, bool Fractional) {
  return isPowerOf2_32(LMUL) && LMUL <= 8 && (!Fractional || LMUL != 1);
}

unsigned encodeVTYPE(RISCIVII::VLMUL VLMUL, unsigned SEW, bool TailAgnostic,
                     bool MaskAgnostic);

inline static RISCIVII::VLMUL getVLMUL(unsigned VType) {
  unsigned VLMUL = VType & 0x7;
  return static_cast<RISCIVII::VLMUL>(VLMUL);
}

// Decode VLMUL into 1,2,4,8 and fractional indicator.
std::pair<unsigned, bool> decodeVLMUL(RISCIVII::VLMUL VLMUL);

inline static unsigned decodeVSEW(unsigned VSEW) {
  assert(VSEW < 8 && "Unexpected VSEW value");
  return 1 << (VSEW + 3);
}

inline static unsigned getSEW(unsigned VType) {
  unsigned VSEW = (VType >> 3) & 0x7;
  return decodeVSEW(VSEW);
}

inline static bool isTailAgnostic(unsigned VType) { return VType & 0x40; }

inline static bool isMaskAgnostic(unsigned VType) { return VType & 0x80; }

void printVType(unsigned VType, raw_ostream &OS);

} // namespace RISCIVVType

} // namespace llvm

#endif
