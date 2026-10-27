module

public import Certificates.Kernel.HN1408.AKDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Check

public section

namespace CFSG.KD.HN1408.R0K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.KD.HN1408.CzT CFSG.KD.HN1408.AK

@[expose] noncomputable def sqK (T : Nat → Nat) (Z : Nat) : Bool :=
  strictB (pt Z 0) fun z0 => strictB (pt Z 1) fun z1 =>
    allN 256 fun p => strictB (T p) fun R => strictB (pt R (pt R 0)) fun s0 =>
      strictB (pt R (pt R 1)) fun s1 => bIf(isBase s0 s1 0 1, true, isBase s0 s1 z0 z1)

@[expose] noncomputable def normRow (T : Nat → Nat) (C X : Nat) : Bool :=
  strictB (pt C 0) fun c0 => strictB (pt C 1) fun c1 =>
  strictB (pt C (pt X 0)) fun a0 => strictB (pt C (pt X 1)) fun a1 =>
  strictB (pt X c0) fun b0 => strictB (pt X c1) fun b1 =>
    bAnd(anyK 256 fun p => isBase (pt (T p) c0) (pt (T p) c1) a0 a1,
      anyK 256 fun q => isBase (pt C (pt (T q) 0)) (pt C (pt (T q) 1)) b0 b1)

@[expose] noncomputable def normK (G X T : Nat → Nat) : Bool :=
  allN 2 fun l => strictB (G l) fun C => allN 7 fun j => normRow T C (X j)

@[expose] noncomputable def interK (X0 X1 X2 X3 X4 X5 e : Nat) (T : Nat → Nat) : Bool :=
  allN 64 fun k => strictB (itP X0 X1 X2 X3 X4 X5 k 0) fun i0 =>
    strictB (itP X0 X1 X2 X3 X4 X5 k 1) fun i1 =>
      bIf(anyK 256 fun p => isBase (pt (T p) 0) (pt (T p) 1) i0 i1,
        Nat.beq (bilC k e) 0, bIf(Nat.beq (bilC k e) 0, false, true))

@[expose] noncomputable def etaB (u : Nat) : Bool := bAnd(Nat.beq (bilC u 1) 0, Nat.beq (lamC u) 0)

@[expose] noncomputable def eichB (X0 X1 X2 X3 X4 X5 w R u : Nat) : Bool :=
  strictB (pt R 0) fun r0 => strictB (pt R 1) fun r1 =>
    allN 64 fun k => strictB (eichC w u k) fun k' =>
      bAnd(Nat.beq (pt R (itP X0 X1 X2 X3 X4 X5 k 0)) (itP X0 X1 X2 X3 X4 X5 k' r0),
        Nat.beq (pt R (itP X0 X1 X2 X3 X4 X5 k 1)) (itP X0 X1 X2 X3 X4 X5 k' r1))

@[expose] noncomputable def eichK (X0 X1 X2 X3 X4 X5 w : Nat) (T : Nat → Nat) : Bool :=
  allN 256 fun p => strictB (T p) fun R =>
    anyK 64 fun u => bAnd(etaB u, eichB X0 X1 X2 X3 X4 X5 w R u)

@[expose] noncomputable def surjK (X0 X1 X2 X3 X4 X5 w : Nat) (T : Nat → Nat) : Bool :=
  allN 64 fun u => bIf(etaB u, anyK 256 fun p => strictB (T p) fun R =>
    eichB X0 X1 X2 X3 X4 X5 w R u, true)

@[expose] noncomputable def withU (F : Nat → Nat → Nat → Nat → Nat → Nat → Bool) : Bool :=
  strictB (U 0) fun X0 => strictB (U 1) fun X1 => strictB (U 2) fun X2 => strictB (U 3) fun X3 =>
    strictB (U 4) fun X4 => strictB (U 5) fun X5 => F X0 X1 X2 X3 X4 X5

@[expose] noncomputable def mzB (A B H Z g0 g1 : Nat) : Bool :=
  strictB (pt A (pt B (pt H 0))) fun l0 => strictB (pt A (pt B (pt H 1))) fun l1 =>
  strictB (pt H g0) fun r0 => strictB (pt H g1) fun r1 =>
    bIf(isBase l0 l1 r0 r1, true, isBase l0 l1 (pt Z r0) (pt Z r1))

@[expose] noncomputable def faithRow (X0 X1 X2 X3 X4 X5 X6 Z n : Nat) (T : Nat → Nat) (A B : Nat) :
    Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    bIf(bAnd(mzB A B X0 Z g0 g1, bAnd(mzB A B X1 Z g0 g1, bAnd(mzB A B X2 Z g0 g1,
        bAnd(mzB A B X3 Z g0 g1, bAnd(mzB A B X4 Z g0 g1, bAnd(mzB A B X5 Z g0 g1,
          mzB A B X6 Z g0 g1)))))),
      anyK n (fun p => isBase g0 g1 (pt (T p) 0) (pt (T p) 1)), true)

@[expose] noncomputable def faithK (T0 T1 X : Nat → Nat) (Z n : Nat) (T : Nat → Nat) : Bool :=
  strictB (X 0) fun X0 => strictB (X 1) fun X1 => strictB (X 2) fun X2 => strictB (X 3) fun X3 =>
    strictB (X 4) fun X4 => strictB (X 5) fun X5 => strictB (X 6) fun X6 => strictB Z fun Z =>
      czScan T0 T1 (faithRow X0 X1 X2 X3 X4 X5 X6 Z n T)

@[expose] noncomputable def commWK (ws : List (List Nat)) (Z : Nat) : Bool :=
  allN ws.length fun j => commP (WK (ws.getD j [])) Z

@[expose] def dg5 (x d : Nat) : Nat := x / 5 ^ d % 5

@[expose] def a5Mul (x y : Nat) : Nat :=
  dg5 x (dg5 y 0) + 5 * dg5 x (dg5 y 1) + 25 * dg5 x (dg5 y 2) + 125 * dg5 x (dg5 y 3) +
    625 * dg5 x (dg5 y 4)

end CFSG.KD.HN1408.R0K

end
