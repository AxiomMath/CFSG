
module

public import Certificates.Data.Kernel.HMathieu.Roots
public import Certificates.Kernel.HMathieu.Odd
public import Certificates.Kernel.HMathieu.T22
public import Certificates.Kernel.HMathieu.T23
public import Certificates.Kernel.HMathieu.T24

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.Roots

open CFSG.KC.HMathieu

@[expose] noncomputable def c7074tab (k : Nat) : Nat × List Nat × List Nat :=
  if k < 14 then
    (if k < 5 then 1 else if k < 10 then 0 else 2, Odd.G.getD k [], Odd.E.getD k [])
  else [(2, T22.gens, T22.E), (1, T23.gens, T23.E), (0, T24.gens, T24.E)].getD (k - 14) (0, [], [])

@[expose] noncomputable def c7074roots (k : Nat) : Bool :=
  rootK (c7074tab k).1 12 (c7074tab k).2.1 (c7074tab k).2.2

#kc_each c7074roots 0 17

end CertificateChecks.KernelHMathieu.Roots

end
