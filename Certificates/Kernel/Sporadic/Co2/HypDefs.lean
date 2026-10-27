module

public import Certificates.Data.Kernel.Spor.CommBase
public import Certificates.Kernel.Sporadic.Co2.ChainAD

public section

namespace CertificateChecks.KernelSpor.Co2H

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def siftP (G : Nat) : Bool :=
  siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) KernelSpor.Co2A.LR KernelSpor.Co2A.TRI
    KernelSpor.Co2A.BP 6 0 G

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 2300 12 (mask 12) p q

@[expose] noncomputable def pow5 (p : Nat) : Nat := c p (c p (c p (c p p)))

@[expose] noncomputable def perm (p q : Nat) : Bool := permOK 2300 12 (mask 12) (2300 * 12) p q

@[expose] noncomputable def letL (LS : List Nat) (R m z : Nat) : Nat :=
  bif Nat.blt z m then LS.getD z 0 else bif Nat.beq z m then R else LS.getD (z - 1) 0

@[expose] noncomputable def letOK (L : Nat → Nat) (R m : Nat) : Bool :=
  allN m (fun z => bAnd(perm (L z) (L (m + 1 + z)), bAnd(siftP (L z),
    bAnd(Nat.beq (c (L z) R) (c R (L z)), Nat.beq (pow5 (L z)) (pidn 2300 12)))))

@[expose] noncomputable def neqP (p q : Nat) : Bool :=
  notB (allN 2300 (fun i => Nat.beq (pg 12 (mask 12) p i) (pg 12 (mask 12) q i)))

@[expose] noncomputable def e8OK (a b d : Nat) : Bool :=
  bAnd(perm a a, bAnd(perm b b, bAnd(perm d d,
  bAnd(siftP a, bAnd(siftP b, bAnd(siftP d,
  bAnd(Nat.beq (c a b) (c b a), bAnd(Nat.beq (c a d) (c d a), bAnd(Nat.beq (c b d) (c d b),
  bAnd(neqP a (pidn 2300 12), bAnd(neqP b (pidn 2300 12), bAnd(neqP d (pidn 2300 12),
  bAnd(neqP a b, bAnd(neqP a d, bAnd(neqP b d, neqP d (c a b))))))))))))))))

end CertificateChecks.KernelSpor.Co2H

end
