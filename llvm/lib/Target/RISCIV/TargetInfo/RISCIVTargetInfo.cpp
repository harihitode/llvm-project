#include "TargetInfo/RISCIVTargetInfo.h"
#include "llvm/Support/TargetRegistry.h"
using namespace llvm;

Target &llvm::getTheRISCIVTarget() {
  // singleton
  static Target TheRISCIVTarget;
  return TheRISCIVTarget;
}

// Register Target Information for LLVM-Initialization
extern "C" LLVM_EXTERNAL_VISIBILITY void LLVMInitializeRISCIVTargetInfo() {
  RegisterTarget<Triple::risciv> X(getTheRISCIVTarget(), "risciv",
                                   "pretty and cute RISC-IV", "RISCIV");
}
