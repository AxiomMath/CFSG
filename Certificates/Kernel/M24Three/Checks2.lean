module

public import Certificates.Kernel.M24Three.Recs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000

public section

namespace CFSG.KD.M24Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH

@[expose] noncomputable def wp (W len q : Nat) : Nat :=
  wpt 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) W len q

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 24 5 (mask 5) p q

@[expose] noncomputable def idK : Nat := pidn 24 5

@[expose] noncomputable def lv0K (l b q : Nat) : Bool :=
  strictB (TW (Nat.add (Nat.mul 24 l) q)) fun W => strictB (TL (Nat.add (Nat.mul 24 l) q)) fun L =>
    Nat.beq (wp W L b) q

@[expose] noncomputable def lv1K (l b p q : Nat) : Bool :=
  bIf(Nat.beq q p, true,
    strictB (TW (Nat.add (Nat.mul 24 l) q)) fun W => strictB (TL (Nat.add (Nat.mul 24 l) q)) fun L =>
      bAnd(Nat.beq (wp W L b) q, Nat.beq (wp W L p) p))

@[expose] noncomputable def lv2K (l b p p' q : Nat) : Bool :=
  bIf(Nat.beq q p, true, bIf(Nat.beq q p', true,
    strictB (TW (Nat.add (Nat.mul 24 l) q)) fun W => strictB (TL (Nat.add (Nat.mul 24 l) q)) fun L =>
      bAnd(Nat.beq (wp W L b) q, bAnd(Nat.beq (wp W L p) p, Nat.beq (wp W L p') p'))))

theorem ch12613_lv : bAnd(allN 24 (lv0K 0 0), bAnd(allN 24 (lv1K 1 3 0), bAnd(allN 24 (lv2K 2 5 0 3),
    bAnd(allN 24 (lv1K 3 17 0), allN 24 (lv2K 4 13 0 17))))) = true := by
  quickRfl

@[expose] noncomputable def selK (e y : Nat) : Bool :=
  bIf(Nat.beq y idK, false, strictB (pc y y) fun y2 => bIf(Nat.beq y2 idK, true,
    strictB (pc y2 y2) fun y4 =>
      bIf(Nat.beq e 0, Nat.beq (pc y4 y) idK, Nat.beq (pc y4 (pc y2 y)) idK)))

@[expose] noncomputable def cvAK (i : Nat) : Bool :=
  strictB (CA.T i) fun y => bIf(selK 0 y,
    strictB (CvA i) fun c => strictB (Nat.land c 65535) fun j => strictB (Nat.shiftRight c 16)
      fun k => bAnd(Nat.blt j 3, bAnd(Nat.blt k CA.cnt,
        strictB (CA.T k) fun e => eq22 24 5 (mask 5) y e e (EL (Nat.add 12 j)))), true)

@[expose] noncomputable def cvBK (i : Nat) : Bool :=
  strictB (CB.T i) fun y => bIf(selK 1 y,
    strictB (CvB i) fun c => strictB (Nat.land c 65535) fun j => strictB (Nat.shiftRight c 16)
      fun k => bAnd(Nat.blt j 3, bAnd(Nat.blt k CB.cnt,
        strictB (CB.T k) fun e => eq22 24 5 (mask 5) y e e (EL (Nat.add 18 j)))), true)

@[expose] noncomputable def cvA (i : Nat) : Bool := allBlk (Nat.mul i 60) cvAK 60
@[expose] noncomputable def cvB (i : Nat) : Bool := allBlk (Nat.mul i 56) cvBK 56

#kc_slice_range cvA ch12613cvA_ 0 18
#kc_slice_range cvB ch12613cvB_ 0 9

@[expose] noncomputable def sylK (i : Nat) : Bool :=
  strictB (S.T i) fun e => bIf(Nat.beq e idK, true,
    strictB (SL i) fun d => strictB (Nat.land d 65535) fun L => strictB (Nat.shiftRight d 16)
      fun c => bAnd(Nat.blt c 2,
        strictB (wperm 24 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) (SW i) L) fun u =>
          eq22 24 5 (mask 5) u e (EL c) u))

theorem ch12613_syl : allN S.cnt sylK = true := by quickRfl

@[expose] noncomputable def witK (r h o : Nat) : Bool :=
  strictB (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) fun z => ordIs 24 (pg 5 (mask 5) z) o

theorem ch12613_wit : bAnd(witK 12 15 3, bAnd(witK 13 16 3, bAnd(witK 14 17 15,
    bAnd(witK 18 21 3, bAnd(witK 19 22 3, witK 20 23 3))))) = true := by
  quickRfl

end CFSG.KD.M24Three

end
