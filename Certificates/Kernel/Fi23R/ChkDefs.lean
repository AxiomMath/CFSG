module

public import Certificates.Data.Kernel.Fi23R.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23R.Wits

public section

namespace CFSG.KD.Fi23R

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K

@[expose] noncomputable def wr (r k : Nat) : Nat :=
  strictN (Nat.add (Nat.mul r (nat_lit 990)) (Nat.shiftRight k (nat_lit 5))) fun l =>
    fld(W l, Nat.mul (nat_lit 32) (Nat.land k (nat_lit 31)), nat_lit 4294967295)

@[expose] def wX : List Nat := [129, 43]

@[expose] def wXC : List Nat := [167, 129, 43]

@[expose] def w53 : List Nat := 181 :: wXC

@[expose] def W0n : List Nat := [41, 39, 41, 39, 41, 39, 40, 39, 41, 39, 40, 39]
@[expose] def W1n : List Nat :=
  [40, 39, 41, 39, 41, 39, 40, 39, 41, 39, 41, 39, 40, 39, 41, 39, 40, 39, 40, 39]
@[expose] def W2n : List Nat := [40, 39, 40, 39, 40, 39, 40, 39, 41, 39]
@[expose] def WWn : List Nat := [40, 39, 40, 40, 39, 40, 40]

@[expose] def cws (wR : List Nat) (e₀ e₁ e₂ : Nat) (o₀ o₁ o₂ : Bool) : List (List Nat) :=
  [brayW wR W0n e₀ o₀, brayW wR W1n e₁ o₁, brayW wR W2n e₂ o₂]

@[expose] def cw1 : List (List Nat) := cws wX 2 2 3 true true false
@[expose] def cw2 : List (List Nat) := cws wXC 30 9 9 false false false

@[expose] def u2W : List Nat := [39, 43, 39, 43]
@[expose] def u3W : List Nat := invW WWn ++ [43] ++ WWn ++ u2W

@[expose] def gU : List Nat := [39, 53, 69, 79, 91, 104, 145, 159, 161, 187, 195, 205, 208, 218, 250]
@[expose] def gT : List Nat :=
  [53, 69, 91, 104, 195, 205, 208, 218, 655, 1428, 1795, 2345, 2617, 2787, 2836]

@[expose] noncomputable def cmB (wY : List Nat) (g : Nat) : Bool :=
  eqB G ((128 + g) :: wY) (wY ++ [128 + g])

@[expose] noncomputable def witB (wR : List Nat) (cs : List (List Nat)) : Bool :=
  cs.all fun c => eqB G (wR ++ c) (c ++ wR)

@[expose] noncomputable def baseK : Bool :=
  eqB G [43, 43] [] && witB wX cw1 && witB wXC cw2 &&
    eqB G (u2W ++ u2W) [] && eqB G (u3W ++ u3W) [] &&
    !(Nat.beq (wa G u2W 2) 2) && !(Nat.beq (wa G u3W 2) 2) &&
    (0 :: gU).all (cmB wX) && (0 :: gT).all (cmB wXC)

@[expose] noncomputable def hPts : Bool :=
  Nat.beq (tb G 43 53) 53 && Nat.beq (tA G 1 53) 53 && Nat.beq (tA G 39 53) 53

@[expose] noncomputable def hCnt (lo len : Nat) : Nat := cntS (fxW G w53) lo len

@[expose] noncomputable def uCnt (lo len : Nat) : Nat := cntS (fxW G (wX ++ [167])) lo len

@[expose] noncomputable def exU (k : Nat) : Bool := bIf(Nat.beq k 0, true, Nat.beq k 1)
@[expose] noncomputable def exT (k : Nat) : Bool := bIf(exU k, true, Nat.beq k 39)

@[expose] noncomputable def uScan (lo len : Nat) : Bool := orbSl G wX exU (wr 0) gU 39 39 lo len
@[expose] noncomputable def tScan (lo len : Nat) : Bool := orbSl G wXC exT (wr 1) gT 53 53 lo len

@[expose] noncomputable def cmQ (wR : List Nat) (cs : List (List Nat)) (x : Nat) : Bool :=
  fxW G wR x && fxW G (commW (cs.getD 1 []) (cs.getD 0 [])) x &&
    fxW G (commW (cs.getD 2 []) (cs.getD 0 [])) x

@[expose] noncomputable def c1Cnt (lo len : Nat) : Nat := cntS (cmQ wX cw1) lo len
@[expose] noncomputable def c2Cnt (lo len : Nat) : Nat := cntS (cmQ wXC cw2) lo len
@[expose] noncomputable def u2Cnt (lo len : Nat) : Nat := cntS (fxW G u2W) lo len
@[expose] noncomputable def u3Cnt (lo len : Nat) : Nat := cntS (fxW G u3W) lo len

@[expose] noncomputable def hunt0 : Bool := Nat.beq (hCnt 0 12500) 71
@[expose] noncomputable def hunt1 : Bool := Nat.beq (hCnt 12500 12500) 55
@[expose] noncomputable def hunt2 : Bool := Nat.beq (hCnt 25000 6671) 57
@[expose] noncomputable def uniq0 : Bool := Nat.beq (uCnt 0 23684) 141
@[expose] noncomputable def uniq1 : Bool := Nat.beq (uCnt 23684 7987) 42
@[expose] noncomputable def uscan : Bool := uScan 0 31671
@[expose] noncomputable def tscan0 : Bool := tScan 0 21940
@[expose] noncomputable def tscan1 : Bool := tScan 21940 9731
@[expose] noncomputable def wit1 : Bool := Nat.beq (c1Cnt 0 31671) 2
@[expose] noncomputable def wit2a : Bool := Nat.beq (c2Cnt 0 8727) 0
@[expose] noncomputable def wit2b : Bool := Nat.beq (c2Cnt 8727 8889) 0
@[expose] noncomputable def wit2c : Bool := Nat.beq (c2Cnt 17616 9465) 1
@[expose] noncomputable def wit2d : Bool := Nat.beq (c2Cnt 27081 4590) 1
@[expose] noncomputable def rep2 : Bool := Nat.beq (u2Cnt 0 31671) 695
@[expose] noncomputable def rep3a : Bool := Nat.beq (u3Cnt 0 23684) 141
@[expose] noncomputable def rep3b : Bool := Nat.beq (u3Cnt 23684 7987) 42

end CFSG.KD.Fi23R

end
