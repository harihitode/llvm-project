add_llvm_component_library(LLVMRISCIVAsmParser
  RISCIVAsmParser.cpp

  LINK_COMPONENTS
  MC
  MCParser
  RISCIVDesc
  RISCIVInfo
  Support

  ADD_TO_COMPONENT
  RISCIV
  )
