module

public import Certificates.Kernel.Fi22Rk.Data
public import Certificates.Data.Kernel.Fi22Rk.Tau
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Rk.K

open CFSG.KC.Enum CFSG.KC.Fi22Rk CertificateChecks.KernelFi22Rk

@[expose] noncomputable def SK (k : Nat) : Nat := nIf(Nat.blt k (nat_lit 5), D.AK k, D.GK (Nat.sub k (nat_lit 5)))

@[expose] noncomputable def NB (j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), nat_lit 641, nIf(Nat.beq j (nat_lit 1), nat_lit 911,
    nIf(Nat.beq j (nat_lit 2), nat_lit 738, nIf(Nat.beq j (nat_lit 3), nat_lit 265,
      nIf(Nat.beq j (nat_lit 4), nat_lit 399, nat_lit 1042)))))

@[expose] noncomputable def tau (c : Nat) : Bool :=
  tauAt (SK (Nat.div c (nat_lit 6))) (NB (Nat.mod c (nat_lit 6)))

@[expose] noncomputable def chain (c : Nat) : Bool :=
  allN (nat_lit 64) fun r => strictB (Nat.add (Nat.mul (nat_lit 64) c) r) fun q =>
    bIf(Nat.blt q (nat_lit 3510), chainAt T.C.F D.PK q, true)

open CFSG.KLie.CT (notB) in
theorem negTau : bAnd(notB (tauAt (Nat.add (D.AK 0) (nat_lit 1)) (nat_lit 641)),
    notB (chainAt T.C.F (fun q => nIf(Nat.beq q (nat_lit 0), nat_lit 0, Nat.succ (D.PK q)))
      (CFSG.KC.Enum.pg 12 (CFSG.KS.mask 12) T.C.F 0))) = true := by
  quickRfl

end CertificateChecks.KernelFi22Rk.K

#kc_each CertificateChecks.KernelFi22Rk.K.tau 0 42
#kc_each CertificateChecks.KernelFi22Rk.K.chain 0 55

end
