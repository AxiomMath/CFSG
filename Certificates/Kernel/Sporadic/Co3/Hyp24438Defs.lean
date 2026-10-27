module

public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CertificateChecks.KernelSpor.Co3H

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CommBase

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 276 9 (mask 9) p q

@[expose] noncomputable def pow5 (p : Nat) : Nat := c p (c p (c p (c p p)))

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 276 9 (mask 9) (276 * 9) p

@[expose] noncomputable def perm (p q : Nat) : Bool := permOK 276 9 (mask 9) (276 * 9) p q

@[expose] noncomputable def msift (p : Nat) : Bool :=
  bAnd(CertificateChecks.KernelSpor.Co3Text.hiOK p, CertificateChecks.KernelSpor.Co3C.sift p)

@[expose] noncomputable def neqP (p q : Nat) : Bool :=
  notB (allN 276 (fun i => Nat.beq (pg 9 (mask 9) p i) (pg 9 (mask 9) q i)))

@[expose] noncomputable def letL (LS : List Nat) (R m z : Nat) : Nat :=
  bif Nat.blt z m then LS.getD z 0 else bif Nat.beq z m then R else LS.getD (z - 1) 0

@[expose] noncomputable def letOK (L : Nat → Nat) (R m : Nat) : Bool :=
  allN m (fun z => bAnd(cn (L z), bAnd(perm (L z) (L (m + 1 + z)), bAnd(msift (L z),
    bAnd(Nat.beq (c (L z) R) (c R (L z)), Nat.beq (pow5 (L z)) (pidn 276 9))))))

@[expose] noncomputable def e8OK (a b d : Nat) : Bool :=
  bAnd(cn a, bAnd(cn b, bAnd(cn d, bAnd(perm a a, bAnd(perm b b, bAnd(perm d d,
  bAnd(msift a, bAnd(msift b, bAnd(msift d,
  bAnd(Nat.beq (c a b) (c b a), bAnd(Nat.beq (c a d) (c d a), bAnd(Nat.beq (c b d) (c d b),
  bAnd(neqP a (pidn 276 9), bAnd(neqP b (pidn 276 9), bAnd(neqP d (pidn 276 9),
  bAnd(neqP a b, bAnd(neqP a d, bAnd(neqP b d, neqP d (c a b)))))))))))))))))))

end CertificateChecks.KernelSpor.Co3H

end
