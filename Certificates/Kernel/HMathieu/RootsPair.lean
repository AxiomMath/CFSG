module

public import Certificates.Data.Kernel.HMathieu.RootsPair
public import Certificates.Kernel.HMathieu.Odd
public import Certificates.Kernel.HMathieu.T12

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.RootsPair

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

@[expose] noncomputable def c7112tab (k : Nat) : List Nat × List Nat :=
  if k = 0 then (T12.gens, T12.E) else (Odd.G.getD (k + 13) [], Odd.E.getD (k + 13) [])

@[expose] noncomputable def c7112roots (k : Nat) : Bool :=
  rootPairK 12 (c7112tab k).1 (c7112tab k).2

#kc_each c7112roots 0 4

end CertificateChecks.KernelHMathieu.RootsPair

end
