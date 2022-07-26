add_llvm_component_library(LLVMRISCIVDesc
  RISCIVAsmBackend.cpp
  RISCIVBaseInfo.cpp
  RISCIVELFObjectWriter.cpp
  RISCIVInstPrinter.cpp
  RISCIVMCAsmInfo.cpp
  RISCIVMCCodeEmitter.cpp
  RISCIVMCExpr.cpp
  RISCIVMCTargetDesc.cpp
  RISCIVMatInt.cpp
  RISCIVTargetStreamer.cpp
  RISCIVELFStreamer.cpp

  LINK_COMPONENTS
  MC
  RISCIVInfo
  Support

  ADD_TO_COMPONENT
  RISCIV
)
