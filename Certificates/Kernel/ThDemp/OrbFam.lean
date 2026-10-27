module

public import Certificates.Kernel.ThDemp.OrbData

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp

@[expose] noncomputable def bF (k : Nat) : Bool :=
  batchChk dempData orbData (Nat.div k (nat_lit 24)) (Nat.mod k (nat_lit 24))

@[expose] noncomputable def cF (k : Nat) : Bool :=
  crossChk dempData orbData (Nat.add (nat_lit 5) (Nat.mul (nat_lit 2) (Nat.div k (nat_lit 24))))
    (Nat.add (nat_lit 6) (Nat.mul (nat_lit 2) (Nat.div k (nat_lit 24)))) (Nat.mod k (nat_lit 24))

@[expose] noncomputable def kF (i : Nat) : Bool := kyChk dempData orbData i

@[expose] noncomputable def lF (i : Nat) : Bool := lowChk dempData orbData i

end CertificateChecks.KernelThDemp

end
