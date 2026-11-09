module

public import Certificates.Kernel.LyGlue.Flat

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition

@[expose] noncomputable def cdPt (len e a : Nat) : Nat := wptE cL dL len e a

@[expose] noncomputable def uLen (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 1, nIf(Nat.beq k 1, 19, nIf(Nat.beq k 2, 31, 33)))

@[expose] noncomputable def sel4 (k a0 a1 a2 a3 : Nat) : Nat :=
  nIf(Nat.beq k 0, a0, nIf(Nat.beq k 1, a1, nIf(Nat.beq k 2, a2, a3)))

@[expose] noncomputable def yBlkK (e0 e1 e2 e3 : Nat) : Bool :=
  blkOK 66825 1080 4 11 FY (fun k a => cdPt (uLen k) (sel4 k e0 e1 e2 e3) a) UH.F

@[expose] noncomputable def tLen (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 24, nIf(Nat.beq k 1, 31, nIf(Nat.beq k 2, 33, 35)))

@[expose] noncomputable def tBlkK (e0 e1 e2 e3 : Nat) : Bool :=
  blkOK 66825 243 4 8 FT (fun k a => cdPt (tLen k) (sel4 k e0 e1 e2 e3) a) GH.F

@[expose] noncomputable def lyPtE (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => nIf(Nat.beq k 1, cL (ih a), nIf(Nat.beq k 2, dL (ih a), ih a))) L

@[expose] def wShort : List Nat :=
  [2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 1, 2, 2, 1, 2]

@[expose] def yShort : List Nat :=
  [2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 1]


@[expose] def uEs (w : List Int) : List Nat :=
  w.flatMap fun l => if 0 < l then cdE (Ly0.uWords.getD (l.toNat - 1) [])
    else cdE (McLMultiplier.invW (Ly0.uWords.getD ((-l).toNat - 1) []))

@[expose] def cdInv (L : List Nat) : List Nat :=
  L.reverse.flatMap fun k => if k = 2 then [2, 2] else [k]

@[expose] noncomputable def lyBase3 (A B : List Nat) : Bool :=
  bAnd(Nat.beq (lyPtE A 0) (lyPtE B 0),
    bAnd(Nat.beq (lyPtE A 3) (lyPtE B 3), Nat.beq (lyPtE A 1) (lyPtE B 1)))

@[expose] noncomputable def lyConjK (T L : List Nat) : Bool :=
  bIf(lyBase3 (T ++ L) (L ++ T), true, lyBase3 (T ++ L) (cdInv L ++ T))

@[expose] noncomputable def txyConjK : Bool :=
  allN 5 fun j => bAnd(lyConjK (uEs (Ly1080.txyWords.getD j [])) (cdE Ly0.wordX),
    bAnd(lyConjK (uEs (Ly1080.txyWords.getD j [])) yShort,
      lyConjK (uEs (Ly1080.txyWords.getD j [])) wShort))

@[expose] noncomputable def imgK : Bool :=
  bAnd(lyBase3 yShort (uE yU), lyBase3 (cdE Ly0.wordX) (uE xU))

@[expose] def txE (w : List Int) : List Nat :=
  w.flatMap fun l => if 0 < l then cdE (Glue.txWords.getD (l.toNat - 1) [])
    else cdE (McLMultiplier.invW (Glue.txWords.getD ((-l).toNat - 1) []))

@[expose] noncomputable def agreeK : Bool :=
  allN 5 fun j => lyBase3 (uEs (Ly1080.txyWords.getD j [])) (txE (Ly243.txyWords.getD j []))

end CertificateChecks.KernelLy

end
