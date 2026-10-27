module

public import Certificates.Kernel.He7030.Data
public import Certificates.Kernel.HeDc.Defs
public import Certificates.Data.Kernel.PtEnum

public noncomputable section

namespace CFSG.KD.He7030

open CFSG.KC.PtEnum CFSG.KC.E64F CFSG.KC.SLDc CFSG.KD.HeDc

@[expose] def base : List Nat := [0, 1, 3, 4, 2]

@[expose] def invW (w : List Nat) : List Nat :=
  w.reverse.flatMap fun l => bif Nat.beq l 0 then [0] else [1, 1, 1, 1, 1, 1]

@[expose] def yW (k : Nat) : List (List Nat) := bif Nat.beq k 3 then Dt.y3 else Dt.y4

@[expose] def eT (k : Nat) : Array (List Nat) := bif Nat.beq k 3 then Dt.T3 else Dt.T4

@[expose] def ePar (k : Nat) : Array Nat := bif Nat.beq k 3 then Dt.par3 else Dt.par4

@[expose] def eLab (k : Nat) : Array Nat := bif Nat.beq k 3 then Dt.lab3 else Dt.lab4

@[expose] def eCl (k : Nat) : Array Nat := bif Nat.beq k 3 then Dt.cl3 else Dt.cl4

@[expose] def YG (k : Nat) : List (Nat → Nat) := (yW k).map (wordF L)

@[expose] def mW (k : Nat) : List Nat := (HeDc.J.mw.getD k []).headD []

@[expose] def VG (k : Nat) : List ((Nat → Nat) × (Nat → Nat)) :=
  [(L 2, L 6), (L 3, L 7), (L 4, L 8), (L 5, L 9), (wordF L (mW k), wordF L (invW (mW k)))]

@[expose] def lows (k : Nat) : List Nat := bif Nat.beq k 3 then [2, 5] else [2, 9]

@[expose] def invB (f g : Nat → Nat) : Bool := base.all fun b => Nat.beq (f (g b)) b

@[expose] def ordChk (k : Nat) : Bool :=
  ((yW k).all fun w => w.all fun l => Nat.blt l 2) && ((mW k).all fun l => Nat.blt l 2) &&
  ((yW k).all fun w => base.all fun b => Nat.beq (wordF L w (wordF L w (wordF L w b))) b) &&
  invB (wordF L (mW k)) (wordF L (invW (mW k)))

@[expose] def enumChk (k : Nat) : Bool :=
  Nat.beq (eT k).size 192 && rowsOKF 8330 base (YG k) (eT k) (ePar k) (eLab k) (eCl k)

@[expose] def normChk (k : Nat) : Bool :=
  (VG k).all fun v => (yW k).all fun w =>
    (eT k).contains (base.map fun q => v.1 (wordF L w (v.2 q)))

@[expose] def labChk (k : Nat) : Bool :=
  (lows k).all fun j => (yW k).all fun w => (Om j).lbl.toList.contains (labF (wordF L w) Δ)

end CFSG.KD.He7030

end
