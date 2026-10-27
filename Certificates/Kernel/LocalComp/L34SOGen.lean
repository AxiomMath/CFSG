module

public import Certificates.Kernel.LocalComp.L34Gen
public meta import Certificates.Kernel.LocalComp.L34Gen

public section

namespace CertificateChecks.KernelLC.L34SOGen

open CFSG.PSL3Four.Native CertificateChecks.KernelLC.L34Gen

meta def cstS (k : Nat) (t : Array Nat) : Array Nat :=
  comp 42 (comp 42 gensS[k]! t) (invTab 42 gensS[k]!)

meta def oS := let o := searchSt 3 cstS (r₁T ()); layout o.1 o.2 11 o.1.size

meta def oST : Array (Array Nat) := oS.1
meta def oSE : Array (Array Nat) := oS.2.1
meta def oSS : Array (Array Nat) := oS.2.2.1
meta def oSSI : Array (Array Nat) := oS.2.2.2.1

end CertificateChecks.KernelLC.L34SOGen

end
