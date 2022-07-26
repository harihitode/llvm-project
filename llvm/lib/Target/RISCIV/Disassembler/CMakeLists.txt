add_llvm_component_library(LLVMRISCIVDisassembler
  RISCIVDisassembler.cpp

  LINK_COMPONENTS
  MC
  MCDisassembler
  RISCIVDesc
  RISCIVInfo
  Support

  ADD_TO_COMPONENT
  RISCIV
  )
