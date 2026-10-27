module

public import Certificates.Kernel.HN1408.FixRDefs

public section

namespace CFSG.KD.HN1408.FixR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def closF (YG Y C : Nat → Nat) (nYG nY : Nat) : Bool :=
  allN nY fun k => allN nYG fun l => strictB (f16 (C k) l) fun k' =>
    bAnd(Nat.blt k' nY, Nat.beq (pc (YG l) (Y k)) (Y k'))

@[expose] noncomputable def keyS (X : Nat) : Nat :=
  Nat.add (pt X 1) (Nat.add (Nat.mul 2048 (pt X 2))
    (Nat.add (Nat.mul 4194304 (pt X 3)) (Nat.mul 8589934592 (pt X 4))))

@[expose] noncomputable def distF (Y D : Nat → Nat) (nY : Nat) : Bool :=
  allN nY fun m => strictB (f16 (D m) 0) fun k => bAnd(Nat.blt k nY,
    bIf(Nat.blt (m + 1) nY, Nat.blt (keyS (Y k)) (keyS (Y (f16 (D (m + 1)) 0))), true))

@[expose] noncomputable def witF (Y YI R : Nat → Nat) (nY n X i j : Nat) : Bool :=
  bAnd(Nat.blt i n, bAnd(Nat.blt j nY, Nat.beq X (cyF Y YI j (R i))))

@[expose] noncomputable def covF (Y W : Nat → Nat) (nY : Nat)
    (wit : Nat → Nat → Nat → Nat → Bool) : Bool :=
  allN nY fun k => bIf(Nat.beq k 0, true, strictB (W k) fun w =>
    wit (f16 w 0) (Y k) (f16 w 1) (f16 w 2))

@[expose] noncomputable def wit3 (_c X i j : Nat) : Bool := witF Fix3.Y Fix3.YI Fix3.R 7 500 X i j

@[expose] noncomputable def wit5 (c X i j : Nat) : Bool :=
  bIf(Nat.beq c 0, witF Fix5a.Y Fix5a.YI Fix5a.R 3 168 X i j,
    bIf(Nat.beq c 1, witF Fix5b.Y Fix5b.YI Fix5b.R 3 3360 X i j,
      witF Fix5c.Y Fix5c.YI Fix5c.R 7 720 X i j))

@[expose] noncomputable def wit7 (_c X i j : Nat) : Bool :=
  witF Fix7.Y Fix7.YI Fix7.R 125 288 X i j

end CFSG.KD.HN1408.FixR

end
