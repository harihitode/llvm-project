//===-- TriCoreRegisterBankInfo.cpp -----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// This file implements the targeting of the RegisterBankInfo class for
/// TriCore.
/// \todo This should be generated by TableGen.
//===----------------------------------------------------------------------===//

#include "TriCoreRegisterBankInfo.h"
#include "MCTargetDesc/TriCoreMCTargetDesc.h"
#include "llvm/CodeGen/GlobalISel/RegisterBank.h"
#include "llvm/CodeGen/GlobalISel/RegisterBankInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"

#define GET_TARGET_REGBANK_IMPL
#include "TriCoreGenRegisterBank.inc"

// XXX: Replace this with the tablegen'ed variant once available.
#include "TriCoreGenRegisterBankInfo.def"

using namespace llvm;

TriCoreRegisterBankInfo::TriCoreRegisterBankInfo(const TargetRegisterInfo &TRI)
    : TriCoreGenRegisterBankInfo() {
  static bool AlreadyInit = false;
  // We have only one set of register banks, whatever the subtarget
  // is. Therefore, the initialization of the RegBanks table should be
  // done only once. Indeed the table of all register banks
  // (TriCore::RegBanks) is unique in the compiler. At some point, it
  // will get tablegen'ed and the whole constructor becomes empty.
  if (AlreadyInit)
    return;
  AlreadyInit = true;

  // This constructor is only used for assertions of the register banks and
  // the partial mappings.

  // Check register bank order
  const RegisterBank &DataRegBank = getRegBank(TriCore::DataRegBankID);
  (void)DataRegBank;
  assert(&TriCore::DataRegBank == &DataRegBank &&
         "The order in RegBanks is messed up");

  const RegisterBank &AddrRegBank = getRegBank(TriCore::AddrRegBankID);
  (void)AddrRegBank;
  assert(&TriCore::AddrRegBank == &AddrRegBank &&
         "The order in RegBanks is messed up");

  // Check data register bank coverage
  assert(DataRegBank.covers(*TRI.getRegClass(TriCore::DataRegsRegClassID)) &&
         "Subclass not added?");
  assert(DataRegBank.getSize() == 64 && "DataRegBank should hold up to 64-bit");

  // Check address register bank coverage
  assert(AddrRegBank.covers(*TRI.getRegClass(TriCore::AddrRegsRegClassID)) &&
         "Subclass not added?");
  assert(AddrRegBank.getSize() == 64 && "AddrRegBank should hold up to 64-bit");

  // Check that the to-be-tablegen'ed file is in sync with our expectations.
  // First, the Idx.
  assert(checkPartialMappingIdx(PMI_FirstDataReg, PMI_LastDataReg,
                                {PMI_DataReg, PMI_ExtDataReg}) &&
         "PartialMappingIdx is incorrectly ordered for DataRegs");
  assert(checkPartialMappingIdx(PMI_FirstAddrReg, PMI_LastAddrReg,
                                {PMI_AddrReg, PMI_ExtAddrReg}) &&
         "PartialMappingIdx is incorrectly ordered for AddrRegs");

  // Next, the content.
  // Check partial mapping.
  // use macro to stringify enum value for better assertion message
#define CHECK_PARTIALMAP(Idx, ValStartIdx, ValLength, RB)                      \
  do {                                                                         \
    assert(                                                                    \
        checkPartialMap(PartialMappingIdx::Idx, ValStartIdx, ValLength, RB) && \
        #Idx " is incorrectly initialized");                                   \
  } while (false)

  CHECK_PARTIALMAP(PMI_DataReg, 0, 32, DataRegBank);
  CHECK_PARTIALMAP(PMI_ExtDataReg, 0, 64, DataRegBank);
  CHECK_PARTIALMAP(PMI_AddrReg, 0, 32, AddrRegBank);
  CHECK_PARTIALMAP(PMI_ExtAddrReg, 0, 64, AddrRegBank);

  // get rid of unused function warning in some IDEs
  (void)checkPartialMap;

  // Check value mapping.
  // same as above: use macro to stringify enum
#define CHECK_VALUEMAP_IMPL(Idx, FirstIdx, Size, Offset)                       \
  do {                                                                         \
    assert(checkValueMapImpl(PartialMappingIdx::Idx,                           \
                             PartialMappingIdx::FirstIdx, Size, Offset) &&     \
           #Idx " " #Offset " is incorrectly initialized");                    \
  } while (false)

#define CHECK_VALUEMAP(Idx, FirstIdx, Size)                                    \
  CHECK_VALUEMAP_IMPL(Idx, FirstIdx, Size, 0)

  CHECK_VALUEMAP(PMI_DataReg, PMI_FirstDataReg, 32);
  CHECK_VALUEMAP(PMI_ExtDataReg, PMI_FirstDataReg, 64);
  CHECK_VALUEMAP(PMI_AddrReg, PMI_FirstAddrReg, 32);

  // TODO: Enable this check when 64-bit pointers are supported.
  //  CHECK_VALUEMAP(PMI_ExtAddrReg, PMI_FirstAddrReg, 64);

  // get rid of unused function warning in some IDEs
  (void)checkValueMapImpl;

  // Check the value mapping for 3-operands instructions where all the operands
  // map to the same value mapping.
#define CHECK_VALUEMAP_3OPS(Idx, FirstIdx, Size)                               \
  do {                                                                         \
    CHECK_VALUEMAP_IMPL(Idx, FirstIdx, Size, 0);                               \
    CHECK_VALUEMAP_IMPL(Idx, FirstIdx, Size, 1);                               \
    CHECK_VALUEMAP_IMPL(Idx, FirstIdx, Size, 2);                               \
  } while (false)

  CHECK_VALUEMAP_3OPS(PMI_DataReg, PMI_FirstDataReg, 32);
  CHECK_VALUEMAP_3OPS(PMI_ExtDataReg, PMI_FirstDataReg, 64);
  CHECK_VALUEMAP_3OPS(PMI_AddrReg, PMI_FirstAddrReg, 32);
  CHECK_VALUEMAP_3OPS(PMI_ExtAddrReg, PMI_FirstAddrReg, 64);

  // Check the value mapping for truncations
#define CHECK_VALUEMAP_TRUNC(BankID, PMI_Normal, PMI_Extended)                 \
  do {                                                                         \
    unsigned PartialMapDstIdx = PMI_Normal - PMI_Min;                          \
    unsigned PartialMapSrcIdx = PMI_Extended - PMI_Min;                        \
    (void)PartialMapDstIdx;                                                    \
    (void)PartialMapSrcIdx;                                                    \
                                                                               \
    const ValueMapping *Map = getTruncMapping(BankID, 32, 64);                 \
    (void)Map;                                                                 \
                                                                               \
    assert(Map[0].BreakDown ==                                                 \
               &TriCoreGenRegisterBankInfo::PartMappings[PartialMapDstIdx] &&  \
           Map[0].NumBreakDowns == 1 &&                                        \
           "Trunc dst for " #BankID " is incorrectly initialized");            \
    assert(Map[1].BreakDown ==                                                 \
               &TriCoreGenRegisterBankInfo::PartMappings[PartialMapSrcIdx] &&  \
           Map[1].NumBreakDowns == 1 &&                                        \
           "Trunc src for " #BankID " is incorrectly initialized");            \
  } while (false)

  CHECK_VALUEMAP_TRUNC(TriCore::DataRegBankID, PMI_DataReg, PMI_ExtDataReg);
  CHECK_VALUEMAP_TRUNC(TriCore::AddrRegBankID, PMI_AddrReg, PMI_ExtAddrReg);

  // TODO: check cross register bank copy mappings once implemented

  assert(verify(TRI) && "Invalid register bank information");
}

const RegisterBank &
TriCoreRegisterBankInfo::getRegBankFromRegClass(const TargetRegisterClass &RC,
                                                LLT) const {
  switch (RC.getID()) {
  case TriCore::AddrRegsRegClassID:
  case TriCore::ExtAddrRegsRegClassID:
  case TriCore::ExtAddrRegs_with_asub0_in_ImplStackPtrRegRegClassID:
  case TriCore::ExtAddrRegs_with_asub1_in_ImplAddrRegRegClassID:
  case TriCore::ImplAddrRegRegClassID:
  case TriCore::ImplStackPtrRegRegClassID:
    return getRegBank(TriCore::AddrRegBankID);
  case TriCore::DataRegsRegClassID:
  case TriCore::ExtDataRegsRegClassID:
  case TriCore::ExtDataRegs_with_dsub1_in_ImplDataRegRegClassID:
  case TriCore::ImplDataRegRegClassID:
    return getRegBank(TriCore::DataRegBankID);
  default:
    llvm_unreachable("Register class not supported");
  }
}

const RegisterBankInfo::InstructionMapping &
TriCoreRegisterBankInfo::getSameKindOfOperandsMapping(
    const MachineInstr &MI) const {

  const MachineFunction &MF = *MI.getParent()->getParent();
  const MachineRegisterInfo &MRI = MF.getRegInfo();

  unsigned NumOperands = MI.getNumOperands();
  assert(NumOperands <= 3 &&
         "This code is for instructions with 3 or less operands");

  LLT Ty = MRI.getType(MI.getOperand(0).getReg());
  unsigned Size = Ty.getSizeInBits();
  bool IsAddrReg = Ty.isPointer();

  // get the partial mapping index for the required register bank
  PartialMappingIdx RBIdx = IsAddrReg ? PMI_FirstAddrReg : PMI_FirstDataReg;

#ifndef NDEBUG
  // Make sure all the operands are using similar size by checking that the
  // register bank base offset of the operand is equal to the base offset of the
  // result register bank
  for (unsigned Idx = 1; Idx != NumOperands; ++Idx) {
    LLT OpTy = MRI.getType(MI.getOperand(Idx).getReg());
    assert(
        TriCoreGenRegisterBankInfo::getRegBankBaseIdxOffset(
            RBIdx, OpTy.getSizeInBits()) ==
            TriCoreGenRegisterBankInfo::getRegBankBaseIdxOffset(RBIdx, Size) &&
        "Operand has incompatible size");
    bool IsOpTyAddrReg = OpTy.isPointer();
    (void)IsOpTyAddrReg;
    assert(IsOpTyAddrReg == IsAddrReg && "Operand has incompatible type.");
  }
#endif // NDEBUG

  return getInstructionMapping(DefaultMappingID, 1,
                               getValueMapping(RBIdx, Size), NumOperands);
}

const RegisterBankInfo::InstructionMapping &
TriCoreRegisterBankInfo::getInstrMapping(const MachineInstr &MI) const {
  unsigned OpCode = MI.getOpcode();

  // try the default logic. if this fails, map manually
  if (!isPreISelGenericOpcode(OpCode) || OpCode == TargetOpcode::G_PHI) {
    const RegisterBankInfo::InstructionMapping &Mapping =
        getInstrMappingImpl(MI);
    if (Mapping.isValid())
      return Mapping;
  }

  // Commonly used helpers.
  const MachineFunction &MF = *MI.getParent()->getParent();
  const MachineRegisterInfo &MRI = MF.getRegInfo();
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const TargetRegisterInfo &TRI = *STI.getRegisterInfo();

  switch (OpCode) {
  // Truncation & Extends
  case TargetOpcode::G_TRUNC: {
    // Truncation happens on the same regbank on different sizes.
    const Register DstReg = MI.getOperand(0).getReg();
    const Register SrcReg = MI.getOperand(1).getReg();

    unsigned DstSize = getSizeInBits(DstReg, MRI, TRI);
    unsigned SrcSize = getSizeInBits(SrcReg, MRI, TRI);
    const RegisterBank *DstRB = getRegBank(DstReg, MRI, TRI);
    const RegisterBank *SrcRB = getRegBank(SrcReg, MRI, TRI);

    if (!SrcRB)
      SrcRB = DstRB;

    assert(SrcRB && "Both register banks were null!");

    // Trunc happens on the same reg-bank and therefore we could hard-code
    // a cost, but using copyCost allows us to override the actual cost
    // behavior in the future if needed
    return getInstructionMapping(
        DefaultMappingID, copyCost(*SrcRB, *SrcRB, SrcSize),
        getTruncMapping(SrcRB->getID(), DstSize, SrcSize), MI.getNumOperands());
  }
  // Arithmetic ops.
  case TargetOpcode::G_ADD:
  case TargetOpcode::G_SUB:
  case TargetOpcode::G_MUL:
  case TargetOpcode::G_UMULH:
  case TargetOpcode::G_SDIV:
  case TargetOpcode::G_SREM:
  case TargetOpcode::G_UDIV:
  case TargetOpcode::G_UREM:
  case TargetOpcode::G_FADD:
  case TargetOpcode::G_FSUB:
  case TargetOpcode::G_FMAXNUM:
  case TargetOpcode::G_FMINNUM:
  case TargetOpcode::G_FMUL:
  case TargetOpcode::G_FDIV:
  // Bitwise ops.
  case TargetOpcode::G_AND:
  case TargetOpcode::G_OR:
  case TargetOpcode::G_XOR:
  // Shifts.
  case TargetOpcode::G_SHL:
  case TargetOpcode::G_LSHR:
  case TargetOpcode::G_ASHR:
    return getSameKindOfOperandsMapping(MI);
  default:
    break;
  }

  unsigned NumOperands = MI.getNumOperands();

  // Track the size and bank of each register. We don't do partial mappings.
  SmallVector<unsigned, 4> OpSize(NumOperands);
  SmallVector<PartialMappingIdx, 4> OpRegBankIdx(NumOperands);
  for (unsigned Idx = 0; Idx < NumOperands; ++Idx) {
    auto &MO = MI.getOperand(Idx);

    // Skip if the operand does not have a register
    if (!MO.isReg() || !MO.getReg())
      continue;

    LLT Ty = MRI.getType(MO.getReg());
    OpSize[Idx] = Ty.getSizeInBits();

    // As a first guess, scalars go in DataRegs, pointers in AddrRegs
    if (Ty.isPointer())
      OpRegBankIdx[Idx] = PMI_FirstAddrReg;
    else
      OpRegBankIdx[Idx] = PMI_FirstDataReg;
  }

  unsigned Cost = 1;

  // Some instructions have mixed types but require the same bank. Fine-tune the
  // computed mapping.
  switch (OpCode) {
  case TargetOpcode::G_INTTOPTR:
  case TargetOpcode::G_PTRTOINT: {
    // G_INTTOPTR as well as G_PTRTOINT are allowed to be same-bank or
    // cross-bank. As a default we use the less costly same-bank variant.
    // The RegBank of the src register is preferred to try to avoid a redundant
    // cross-bank copy
    OpRegBankIdx[0] = OpRegBankIdx[1];
    break;
  }
  case TargetOpcode::G_PTR_ADD: {
    // G_PTR_ADD operands must all be one the same regbank
    OpRegBankIdx = {PMI_FirstAddrReg, PMI_FirstAddrReg, PMI_FirstAddrReg};
    break;
  }
  case TargetOpcode::G_MERGE_VALUES:
  case TargetOpcode::G_UNMERGE_VALUES: {
    // Merge and unmerge can only be selected on the data regbank, unless we can
    // use a subregister copy. A subregister copy can be used if we go from 64
    // to 32-bit.
    const unsigned BigTyIdx =
        OpCode == TargetOpcode::G_MERGE_VALUES ? 0 : NumOperands - 1;
    const unsigned SmallTyIdx =
        OpCode == TargetOpcode::G_MERGE_VALUES ? NumOperands - 1 : 0;

    const LLT SmallTy = MRI.getType(MI.getOperand(SmallTyIdx).getReg());
    const LLT BigTy = MRI.getType(MI.getOperand(BigTyIdx).getReg());

    // Check if we can use the default mapping (subregister copy can be used)
    if (SmallTy.getSizeInBits() == 32 && BigTy.getSizeInBits() == 64)
      break;

    // Force data regbank
    for (unsigned Idx = 0; Idx < NumOperands; ++Idx)
      OpRegBankIdx[Idx] = PMI_FirstDataReg;

    break;
  }
  case TargetOpcode::G_SELECT: {
    // TriCore only supports the SEL instruction on data registers, hence all
    // operands must reside on the DataRegBank
    OpRegBankIdx = {PMI_FirstDataReg, PMI_FirstDataReg, PMI_FirstDataReg,
                    PMI_FirstDataReg};
    break;
  }
  case TargetOpcode::G_INSERT: {
    // TriCore only supports INSERT on data registers, hence all
    // operands must reside on the DataRegBank
    OpRegBankIdx = {PMI_FirstDataReg, PMI_FirstDataReg, PMI_FirstDataReg};
    break;
  }
  default:
    break;
  }

  // Construct the computed mapping
  SmallVector<const ValueMapping *, 8> OpdsMapping(NumOperands);
  for (unsigned Idx = 0; Idx < NumOperands; ++Idx) {
    if (MI.getOperand(Idx).isReg() && MI.getOperand(Idx).getReg()) {
      auto Mapping = getValueMapping(OpRegBankIdx[Idx], OpSize[Idx]);
      if (!Mapping->isValid())
        return getInvalidInstructionMapping();

      OpdsMapping[Idx] = Mapping;
    }
  }

  return getInstructionMapping(DefaultMappingID, Cost,
                               getOperandsMapping(OpdsMapping), NumOperands);
}
