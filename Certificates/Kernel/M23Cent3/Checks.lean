module

public import Certificates.Kernel.M23Cent3.Recs
public import Certificates.Data.Kernel.Spor.MulHQ
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.SliceRange

set_option maxRecDepth 400000

public section

namespace CFSG.KD.M23Cent3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

@[expose] noncomputable def cK (p : Nat) : Bool := canonK 23 5 (mask 5) (23 * 5) p

@[expose] noncomputable def invK (p q : Nat) : Bool :=
  bAnd(cK p, bAnd(cK q, invEqK 23 5 (mask 5) (23 * 5) p q))

@[expose] noncomputable def elK (j : Nat) : Bool :=
  bAnd(invK (EL j) (EI j),
    Nat.beq (EL j) (wperm 23 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) (WL j) (LN j)))

@[expose] noncomputable def cmK (p q : Nat) : Bool := eq22 23 5 (mask 5) p q q p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 23 5 (mask 5) p q

@[expose] noncomputable def idK : Nat := pidn 23 5

@[expose] noncomputable def wp (W len q : Nat) : Nat :=
  wpt 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) W len q

theorem ch12641_el : bAnd(invK (GN 0) (GN 2), bAnd(invK (GN 1) (GN 3), allN 11 elK)) = true := by
  quickRfl

theorem ch12641_bind :
    bAnd(Nat.beq CE.k 2, bAnd(Nat.beq (CE.G 0) (pidn 23 5), bAnd(Nat.beq (CE.G 1) (pidn 23 5),
    bAnd(Nat.beq (CE.GI 0) (EL 2), bAnd(Nat.beq (CE.GI 1) (EL 3), bAnd(Nat.beq CE.R (pidn 23 5),
    bAnd(Nat.beq CE.cnt 180, bAnd(penumHdK CE.R CE.cnt 2000 CE.T CE.PL,
    bAnd(Nat.beq S.k 2, bAnd(Nat.beq (S.G 0) (pidn 23 5), bAnd(Nat.beq (S.G 1) (pidn 23 5),
    bAnd(Nat.beq (S.GI 0) (EL 0), bAnd(Nat.beq (S.GI 1) (EL 1), bAnd(Nat.beq S.R (pidn 23 5),
    bAnd(Nat.beq S.cnt 9, bAnd(penumHdK S.R S.cnt 100 S.T S.PL,
    bAnd(Nat.beq (SI 0) (EI 0), Nat.beq (SI 1) (EI 1)))))))))))))))))) = true := by
  quickRfl

@[expose] noncomputable def inF (i : Nat) : Bool :=
  bIf(Nat.beq i 0, true, bIf(Nat.beq i 1, true, bIf(Nat.beq i 2, true,
    bIf(Nat.beq i 10, true, Nat.beq i 15))))

@[expose] noncomputable def fxK (p i : Nat) : Bool :=
  bIf(Nat.beq (pg 5 (mask 5) p i) i, inF i, bIf(inF i, false, true))

theorem ch12641_fix : allN 23 (fxK (EL 0)) = true := by
  quickRfl

theorem ch12641_inv :
    bAnd(eq22 23 5 (mask 5) (EL 10) (EL 0) (EI 0) (EL 10), bIf(Nat.beq (EL 0) (EI 0), false, true)) =
      true := by
  quickRfl

theorem ch12641_comm :
    bAnd(cmK (EL 2) (EL 0), bAnd(cmK (EL 3) (EL 0), bAnd(cmK (EL 4) (EL 0),
    bAnd(cmK (EL 5) (EL 0), bAnd(cmK (EL 6) (EL 0), bAnd(cmK (EL 7) (EL 0),
    bAnd(cmK (EL 8) (EL 0), cmK (EL 9) (EL 0)))))))) = true := by
  quickRfl

@[expose] noncomputable def o2K (y : Nat) : Bool :=
  bIf(Nat.beq y idK, false, Nat.beq (pc y y) idK)

@[expose] noncomputable def o5K (y : Nat) : Bool :=
  bIf(Nat.beq y idK, false, strictB (pc y y) fun y2 => Nat.beq (pc (pc y2 y2) y) idK)

@[expose] noncomputable def witK (r h : Nat) : Bool :=
  strictB (pc (EL r) (pc (EL h) (pc (EL r) (EI h)))) fun z =>
    bIf(Nat.beq z idK, false, Nat.beq (pc z (pc z z)) idK)

theorem ch12641_ord :
    bAnd(o2K (EL 4), bAnd(o5K (EL 5), bAnd(o5K (EL 6),
    bAnd(witK 4 7, bAnd(witK 5 8, witK 6 9))))) = true := by
  quickRfl

@[expose] noncomputable def lvK (l N b : Nat) (f : Nat → Nat → Bool) (k : Nat) : Bool :=
  strictB (Nat.add (Nat.mul 23 l) k) fun e => strictB (PT e) fun q =>
    bAnd(bIf(Nat.beq (Nat.succ k) N, Nat.blt q 23, Nat.blt q (PT (Nat.succ e))),
      strictB (TW e) fun W => strictB (TL e) fun L => bAnd(Nat.beq (wp W L b) q, f W L))

@[expose] noncomputable def fx1 (p W L : Nat) : Bool := Nat.beq (wp W L p) p

theorem ch12641_lv :
    bAnd(allN 23 (lvK 0 23 0 fun _ _ => true),
    bAnd(allN 22 (lvK 1 22 1 fun W L => fx1 0 W L),
    bAnd(allN 21 (lvK 2 21 2 fun W L => bAnd(fx1 0 W L, fx1 1 W L)),
    bAnd(allN 20 (lvK 3 20 10 fun W L => bAnd(fx1 0 W L, bAnd(fx1 1 W L, fx1 2 W L))),
    allN 16 (lvK 4 16 15 fun W L =>
      bAnd(fx1 0 W L, bAnd(fx1 1 W L, bAnd(fx1 2 W L, fx1 10 W L)))))))) = true := by
  quickRfl

@[expose] noncomputable def ceE (i : Nat) : Bool := penumSlK 23 5 (mask 5) (23 * 5) true CE.G CE.GI
  2 CE.cnt CE.T CE.PL CE.POS CE.SRT CE.SRI (Nat.mul i 60) 60
@[expose] noncomputable def ceH (i : Nat) : Bool :=
  slK CE.cnt (hsortPtK 23 5 (mask 5) CE.cnt CE.T CE.HS CE.HSI) (Nat.mul i 60) 60

#kc_slice_range ceE ch12641ceE_ 0 3
#kc_slice_range ceH ch12641ceH_ 0 3

theorem ch12641sE : penumSlK 23 5 (mask 5) (23 * 5) true S.G S.GI 2 S.cnt S.T S.PL S.POS S.SRT
    S.SRI 0 S.cnt = true := by quickRfl
theorem ch12641sH : slK S.cnt (hsortPtK 23 5 (mask 5) S.cnt S.T S.HS S.HSI) 0 S.cnt = true := by
  quickRfl
theorem ch12641sCl : slK (Nat.mul S.cnt 4)
    (findPtK S.cnt S.T (prodQK 23 5 (mask 5) 4 S.T (bothK 2 S.GI SI)) SCl) 0
      (Nat.mul S.cnt 4) = true := by quickRfl

@[expose] noncomputable def selK (y : Nat) : Bool :=
  bIf(Nat.beq y idK, false, strictB (pc y y) fun y2 => bIf(Nat.beq y2 idK, true,
    Nat.beq (pc (pc y2 y2) y) idK))

@[expose] noncomputable def cvK (i : Nat) : Bool :=
  strictB (CE.T i) fun y => bIf(selK y,
    strictB (Cv i) fun c => strictB (Nat.land c 65535) fun j => strictB (Nat.shiftRight c 16)
      fun k => bAnd(Nat.blt j 3, bAnd(Nat.blt k CE.cnt,
        strictB (CE.T k) fun e => eq22 23 5 (mask 5) y e e (EL (Nat.add 4 j)))), true)

@[expose] noncomputable def cv (i : Nat) : Bool := allBlk (Nat.mul i 60) cvK 60

#kc_slice_range cv ch12641cv_ 0 3

@[expose] noncomputable def sylK (i : Nat) : Bool :=
  strictB (S.T i) fun e => bIf(Nat.beq e idK, true,
    strictB (SL i) fun L =>
      strictB (wperm 23 5 (mask 5) (GN 0) (GN 1) (GN 2) (GN 3) (SW i) L) fun u =>
        eq22 23 5 (mask 5) u e (EL 0) u)

theorem ch12641_syl : allN S.cnt sylK = true := by quickRfl

end CFSG.KD.M23Cent3

end
