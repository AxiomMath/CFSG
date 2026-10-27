module

public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CertificateChecks.KernelSpor.SuzH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CommBase

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def pow5 (p : Nat) : Nat := c p (c p (c p (c p p)))

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 1782 11 (mask 11) (1782 * 11) p

@[expose] noncomputable def perm (p q : Nat) : Bool := permOK 1782 11 (mask 11) (1782 * 11) p q

@[expose] noncomputable def neqP (p q : Nat) : Bool :=
  notB (allN 1782 (fun i => Nat.beq (pg 11 (mask 11) p i) (pg 11 (mask 11) q i)))

@[expose] noncomputable def letL (LS : List Nat) (R m z : Nat) : Nat :=
  bif Nat.blt z m then LS.getD z 0 else bif Nat.beq z m then R else LS.getD (z - 1) 0

@[expose] noncomputable def letOK (L : Nat → Nat) (R m : Nat) : Bool :=
  allN m (fun z => bAnd(cn (L z), bAnd(perm (L z) (L (m + 1 + z)), bAnd(OddCore.msift (L z),
    bAnd(Nat.beq (c (L z) R) (c R (L z)), Nat.beq (pow5 (L z)) (pidn 1782 11))))))

@[expose] noncomputable def yOK (Y YI L : Nat → Nat) (m nY : Nat) : Bool :=
  allN nY (fun k => bAnd(cn (Y k), bAnd(perm (Y k) (YI k), bAnd(notB (OddCore.msift (Y k)),
    bAnd(notB (OddCore.msift (c Suz2306.V (Y k))),
    allN (m + 1) (fun z => Nat.beq (c (Y k) (L z)) (c (L z) (Y k))))))))

@[expose] noncomputable def e8OK (a b d : Nat) : Bool :=
  bAnd(cn a, bAnd(cn b, bAnd(cn d, bAnd(perm a a, bAnd(perm b b, bAnd(perm d d,
  bAnd(OddCore.msift a, bAnd(OddCore.msift b, bAnd(OddCore.msift d,
  bAnd(Nat.beq (c a b) (c b a), bAnd(Nat.beq (c a d) (c d a), bAnd(Nat.beq (c b d) (c d b),
  bAnd(neqP a (pidn 1782 11), bAnd(neqP b (pidn 1782 11), bAnd(neqP d (pidn 1782 11),
  bAnd(neqP a b, bAnd(neqP a d, bAnd(neqP b d, neqP d (c a b)))))))))))))))))))

@[expose] noncomputable def foursOK (l li t : Nat) : Bool :=
  bAnd(cn l, bAnd(perm l li, bAnd(OddCore.msift l,
    strictB (c (c (c l t) li) t) (fun C => bAnd(Nat.beq (c C C) (pidn 1782 11),
      neqP C (pidn 1782 11))))))

end CertificateChecks.KernelSpor.SuzH

end
