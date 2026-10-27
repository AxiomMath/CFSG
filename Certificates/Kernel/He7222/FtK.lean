module

public import Certificates.Kernel.He7222.FibK
public import Certificates.Data.Kernel.He7222.Good
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain

@[expose] noncomputable def offK (XR : List (List Nat)) (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k ih => Nat.add ih (lenS (getLs XR k))) j

@[expose] noncomputable def fiK (J N : Nat) (XR FI : List (List Nat)) : Bool :=
  allN J (fun j => allN (lenS (getLs XR j)) (fun r => strictB (Nat.add (offK XR j) r) (fun i =>
    bAnd(Nat.blt i N, bAnd(Nat.beq (getS (getLs FI i) 0) j, Nat.beq (getS (getLs FI i) 1) r)))))

@[expose] noncomputable def ftOK (KTs : List (List Nat)) (FT : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun kt _ ih => bAnd(tupOK KTs kt, ih)) FT

@[expose] noncomputable def frOK (nt : Nat) (FR : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun rec _ ih => bAnd(Nat.blt (getS rec 1) nt, ih)) FR

@[expose] noncomputable def ftK (KTs : List (List (List Nat))) (FI : List (List Nat))
    (FT FR : List (List (List Nat))) (i : Nat) : Bool :=
  strictB (getS (getLs FI i) 0) (fun j =>
    bAnd(ftOK (getLL KTs j) (getLL FT i), frOK (lenLN (getLL FT i)) (getLL FR i)))

theorem ch7222shrA : allN 8 (fun j => Nat.beq (Nat.shiftRight (getS scH j) (Nat.mul 8330 14)) 0) =
    true := by
  quickRfl

@[expose] noncomputable def xrK (XR : List Nat) (n : Nat) : Bool :=
  allN (lenS XR) (fun r => Nat.blt (getS XR r) n)

theorem ch7222xr : (xrK (getLs a0XR 0) (lenLN (getLL a0KC 0)) &&
    xrK (getLs a0XR 1) (lenLN (getLL a0KC 1)) && xrK (getLs t1XR 0) (lenLN (getLL t1KC 1)) &&
    xrK (getLs t1XR 1) (lenLN (getLL t1KC 2)) && xrK (getLs t1XR 2) (lenLN (getLL t1KC 3)) &&
    xrK (getLs t1XR 3) (lenLN (getLL t1KC 5)) && xrK (getLs t1XR 4) (lenLN (getLL t1KC 6))) =
    true := by
  quickRfl

theorem ch7222fia : fiK 2 10 a0XR a0FI = true := by quickRfl
theorem ch7222fit : fiK 5 44 t1XR t1FI = true := by quickRfl
theorem ch7222fta : allN 10 (ftK a0KTs a0FI a0FT a0FR) = true := by quickRfl
theorem ch7222ftt : allN 44 (ftK t1KTs t1FI t1FT t1FR) = true := by quickRfl

end CFSG.KD.He7222

end
