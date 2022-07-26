add_llvm_component_library(LLVMRISCIVInfo
  RISCIVTargetInfo.cpp

  LINK_COMPONENTS
  Support

  ADD_TO_COMPONENT
  RISCIV
  )
