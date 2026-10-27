module

public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CertificateChecks.KernelSpor.McLH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CommBase

@[expose] noncomputable def c (p q : Nat) : Nat := pcomp 275 9 (mask 9) p q

@[expose] noncomputable def pow5 (p : Nat) : Nat := c p (c p (c p (c p p)))

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 275 9 (mask 9) (275 * 9) p

@[expose] noncomputable def perm (p q : Nat) : Bool := permOK 275 9 (mask 9) (275 * 9) p q

@[expose] noncomputable def msift (p : Nat) : Bool :=
  siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) CertificateChecks.KernelCensus.McLC.LR
    CertificateChecks.KernelCensus.McLC.TRI CertificateChecks.KernelCensus.McLC.BP 5 0 p

@[expose] noncomputable def neqP (p q : Nat) : Bool :=
  notB (allN 275 (fun i => Nat.beq (pg 9 (mask 9) p i) (pg 9 (mask 9) q i)))

@[expose] noncomputable def letL (LS : List Nat) (R m z : Nat) : Nat :=
  bif Nat.blt z m then LS.getD z 0 else bif Nat.beq z m then R else LS.getD (z - 1) 0

@[expose] noncomputable def letOK (L : Nat → Nat) (R m : Nat) : Bool :=
  allN m (fun z => bAnd(cn (L z), bAnd(perm (L z) (L (m + 1 + z)), bAnd(msift (L z),
    bAnd(Nat.beq (c (L z) R) (c R (L z)), Nat.beq (pow5 (L z)) (pidn 275 9))))))

@[expose] noncomputable def rootOK (R RI : Nat) : Bool :=
  bAnd(cn R, bAnd(cn RI, invEqK 275 9 (mask 9) (275 * 9) R RI))

@[expose] noncomputable def e8OK (a b d : Nat) : Bool :=
  bAnd(cn a, bAnd(cn b, bAnd(cn d, bAnd(perm a a, bAnd(perm b b, bAnd(perm d d,
  bAnd(msift a, bAnd(msift b, bAnd(msift d,
  bAnd(Nat.beq (c a b) (c b a), bAnd(Nat.beq (c a d) (c d a), bAnd(Nat.beq (c b d) (c d b),
  bAnd(neqP a (pidn 275 9), bAnd(neqP b (pidn 275 9), bAnd(neqP d (pidn 275 9),
  bAnd(neqP a b, bAnd(neqP a d, bAnd(neqP b d, neqP d (c a b)))))))))))))))))))

@[expose] noncomputable def foursOK (l li t : Nat) : Bool :=
  bAnd(Nat.beq (c t t) (pidn 275 9), bAnd(cn l, bAnd(perm l li, bAnd(msift l,
    strictB (c (c (c l t) li) t) (fun C => bAnd(Nat.beq (c C C) (pidn 275 9),
      neqP C (pidn 275 9)))))))

end CertificateChecks.KernelSpor.McLH

end
