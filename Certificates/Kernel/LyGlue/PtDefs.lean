module

public import Certificates.Kernel.LyGlue.TabData

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

@[expose] noncomputable def imgY (k : Nat) : Nat :=
  pmk 1080 11 (fun j => FY (tl (tIdx k) (SY j)))

@[expose] noncomputable def imgW (len e : Nat) : Nat :=
  pmk 1080 11 (fun j => FY (cdPt len e (SY j)))

@[expose] noncomputable def uhInv (k : Nat) : Nat := pinvS 1080 11 (mask 11) (UH.F k)

@[expose] noncomputable def uWord1080 (ws : List Int) : Nat :=
  wprod 1080 11 (mask 11) (letT UH.F uhInv) ws

@[expose] noncomputable def lineK (t a : Nat) : Bool :=
  bIf(eq22 1080 11 (mask 11) t a a t, true,
    eq22 1080 11 (mask 11) t a (pinvS 1080 11 (mask 11) a) t)

@[expose] noncomputable def imgK (ax ay aw : Nat) : Bool :=
  bAnd(Nat.beq ay (uWord1080 yU), bAnd(Nat.beq ax (uWord1080 xU),
    allN 5 (fun j => strictB (uWord1080 (Ly1080.txyWords.getD j [])) fun t =>
      bAnd(lineK t ax, bAnd(lineK t ay, lineK t aw)))))

@[expose] noncomputable def ghInv (k : Nat) : Nat := pinvS 243 8 (mask 8) (GH.F k)

@[expose] noncomputable def uwPt (e0 e1 e2 e3 f0 f1 f2 f3 : Nat) (ws : List Int) (a : Nat) : Nat :=
  wptG (fun k a => cdPt (uLen k) (sel4 k e0 e1 e2 e3) a)
    (fun k a => cdPt (uLen k) (sel4 k f0 f1 f2 f3) a) ws a

@[expose] noncomputable def agreeK (e0 e1 e2 e3 f0 f1 f2 f3 : Nat) : Bool :=
  allN 5 (fun j => strictB (wprod 243 8 (mask 8) (letT GH.F ghInv) (Ly243.txyWords.getD j []))
    fun t => allN 243 (fun k => Nat.beq
      (FT (uwPt e0 e1 e2 e3 f0 f1 f2 f3 (Ly1080.txyWords.getD j []) (ST k)))
      (pg 8 (mask 8) t k)))

end CertificateChecks.KernelLy

end
