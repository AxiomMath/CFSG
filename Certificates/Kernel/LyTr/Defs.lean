module

public import Certificates.Kernel.LyTr.Data

public section

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def p8 (p q : Nat) : Nat := pcomp 243 8 (mask 8) p q
@[expose] noncomputable def id8 : Nat := pidn 243 8
@[expose] noncomputable def c8 (p : Nat) : Bool := canonK 243 8 (mask 8) (243 * 8) p
@[expose] noncomputable def i8 (p r : Nat) : Bool := invEqK 243 8 (mask 8) (243 * 8) p r
@[expose] noncomputable def p11 (p q : Nat) : Nat := pcomp 1080 11 (mask 11) p q
@[expose] noncomputable def id11 : Nat := pidn 1080 11
@[expose] noncomputable def c11 (p : Nat) : Bool := canonK 1080 11 (mask 11) (1080 * 11) p
@[expose] noncomputable def i11 (p r : Nat) : Bool := invEqK 1080 11 (mask 11) (1080 * 11) p r

@[expose] noncomputable def LG (l : Int) : Nat :=
  if 0 < l then GH.F (l.toNat - 1) else GHI ((-l).toNat - 1)
@[expose] noncomputable def LT (l : Int) : Nat :=
  if 0 < l then R2.GI (l.toNat - 1) else R2I ((-l).toNat - 1)
@[expose] noncomputable def LU (l : Int) : Nat :=
  if 0 < l then UH.F (l.toNat - 1) else UHI ((-l).toNat - 1)

@[expose] noncomputable def wK (n w : Nat) (G : Int → Nat) : List Int → Nat
  | [] => pidn n w
  | l :: ws => pcomp n w (mask w) (G l) (wK n w G ws)

@[expose] noncomputable def pw8 (X : Nat) : Nat → Nat
  | 0 => id8
  | e + 1 => p8 X (pw8 X e)

@[expose] noncomputable def ord8 (m X : Nat) : Bool :=
  bAnd(Nat.beq (pw8 X m) id8,
    (CFSG.Sporadic.Schreier.Native.divParts m).all fun e => !Nat.beq (pw8 X e) id8)

@[expose] noncomputable def inL (z a ai : Nat) : Bool := bIf(Nat.beq z a, true, Nat.beq z ai)

@[expose] noncomputable def cj8 (g gi a : Nat) : Nat := p8 (p8 g a) gi

@[expose] noncomputable def GB (m : Nat) : Nat := nIf(Nat.blt m 5, GH.F m, GHI (m - 5))

@[expose] noncomputable def fixL (z zi : Nat) : Bool :=
  allN 3 fun i => inL (cj8 z zi (LH.F i)) (LH.F i) (LHI i)

end CertificateChecks.KernelLyTr

end
