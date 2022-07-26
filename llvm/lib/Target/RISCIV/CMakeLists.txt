add_llvm_component_group(RISCIV)

set(LLVM_TARGET_DEFINITIONS RISCIV.td)

tablegen(LLVM RISCIVGenAsmMatcher.inc -gen-asm-matcher)
tablegen(LLVM RISCIVGenAsmWriter.inc -gen-asm-writer)
tablegen(LLVM RISCIVGenDAGISel.inc -gen-dag-isel)
tablegen(LLVM RISCIVGenDisassemblerTables.inc -gen-disassembler)
tablegen(LLVM RISCIVGenGlobalISel.inc -gen-global-isel)
tablegen(LLVM RISCIVGenInstrInfo.inc -gen-instr-info)
tablegen(LLVM RISCIVGenMCCodeEmitter.inc -gen-emitter)
tablegen(LLVM RISCIVGenMCPseudoLowering.inc -gen-pseudo-lowering)
tablegen(LLVM RISCIVGenRegisterBank.inc -gen-register-bank)
tablegen(LLVM RISCIVGenRegisterInfo.inc -gen-register-info)
tablegen(LLVM RISCIVGenSearchableTables.inc -gen-searchable-tables)
tablegen(LLVM RISCIVGenSubtargetInfo.inc -gen-subtarget)

add_public_tablegen_target(RISCIVCommonTableGen)

add_llvm_target(RISCIVCodeGen
  RISCIVAsmPrinter.cpp
  RISCIVCallLowering.cpp
  RISCIVExpandPseudoInsts.cpp
  RISCIVFrameLowering.cpp
  RISCIVInstrInfo.cpp
  RISCIVInstructionSelector.cpp
  RISCIVISelDAGToDAG.cpp
  RISCIVISelLowering.cpp
  RISCIVLegalizerInfo.cpp
  RISCIVMCInstLower.cpp
  RISCIVMergeBaseOffset.cpp
  RISCIVRegisterBankInfo.cpp
  RISCIVRegisterInfo.cpp
  RISCIVSubtarget.cpp
  RISCIVTargetMachine.cpp
  RISCIVTargetObjectFile.cpp
  RISCIVTargetTransformInfo.cpp

  LINK_COMPONENTS
  Analysis
  AsmPrinter
  Core
  CodeGen
  MC
  RISCIVDesc
  RISCIVInfo
  SelectionDAG
  Support
  Target
  GlobalISel

  ADD_TO_COMPONENT
  RISCIV
  )

add_subdirectory(AsmParser)
add_subdirectory(Disassembler)
add_subdirectory(MCTargetDesc)
add_subdirectory(TargetInfo)
