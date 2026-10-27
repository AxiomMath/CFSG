module

public import Certificates.Kernel.HN1408.M11Defs
public import Certificates.Kernel.HN1408.ClsBData
public import Certificates.Kernel.HN1408.ClsZ1Data

public section

namespace CFSG.KD.HN1408.ClsR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] noncomputable def rootK (w : List Nat) (R : Nat → Nat) : Bool := Nat.beq (R 0) (WK w)

@[expose] noncomputable def repRK (R P : Nat → Nat) (i : Nat) : Bool :=
  strictB (P i) fun q => strictB (f16 q 0) fun p => strictB (f16 q 1) fun k =>
    strictB (f16 q 2) fun j => strictB (WK [j + 1]) fun G =>
      bAnd(Nat.blt p i, bAnd(Nat.blt k 11, bAnd(Nat.blt j 7,
        bIf(Nat.beq k 0, Nat.beq (R i) (pc (pc G (R p)) G),
          Nat.beq (R i) (pc (pc G (pc (pc (MYP k) (R p)) (MYP (11 - k)))) G)))))

@[expose] noncomputable def repSl (R P : Nat → Nat) (n a len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add a d) fun i =>
    bIf(Nat.blt i n, bIf(Nat.beq i 0, true, repRK R P i), true)

@[expose] noncomputable def sortAt (R S : Nat → Nat) (n cnt m : Nat) : Bool :=
  strictB (S m) fun s => bAnd(Nat.blt (f16 s 0) n, bAnd(Nat.blt (f16 s 1) 11,
    bIf(Nat.blt (m + 1) cnt, strictB (S (m + 1)) fun s' =>
      Nat.blt (keyK (R (f16 s 0)) (f16 s 1)) (keyK (R (f16 s' 0)) (f16 s' 1)), true)))

@[expose] noncomputable def sortSl (R S : Nat → Nat) (n cnt a len : Nat) : Bool :=
  allN len fun d => strictB (Nat.add a d) fun m => bIf(Nat.blt m cnt, sortAt R S n cnt m, true)

@[expose] noncomputable def bRep (s : Nat) : Bool := repSl ClsB.R ClsB.P 200 (Nat.mul 50 s) 50

@[expose] noncomputable def bSort (s : Nat) : Bool :=
  sortSl ClsB.R ClsB.S 200 2200 (Nat.mul 550 s) 550

@[expose] noncomputable def z1Rep (s : Nat) : Bool :=
  repSl ClsZ1.R ClsZ1.P 4200 (Nat.mul 100 s) 100

@[expose] noncomputable def z1Sort (s : Nat) : Bool :=
  sortSl ClsZ1.R ClsZ1.S 4200 46200 (Nat.mul 2200 s) 2200

end CFSG.KD.HN1408.ClsR

end
