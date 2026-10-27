module

public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.Kernel.McL5Pairs
public meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.McLFivePairs
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMcL5Pairs

open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.McLFivePairs

meta def strongM : Array (Array Nat) :=
  strongTabs (pairGens (rGens mclFiveDataP)[0]! (rGens mclFiveDataP)[1]!
    ((repT mclFiveDataP).getD excIdx (CFSG.PSL3Four.Native.idTab 275)))

meta def baseM : Array Nat := chainBase

end CertificateChecks.KernelMcL5Pairs

#ks_rawchain CertificateChecks.KernelMcL5Pairs.CH 275 9 35 CertificateChecks.KernelMcL5Pairs.strongM
  CertificateChecks.KernelMcL5Pairs.baseM 4 CFSG.KS.McL5P.dW

end
