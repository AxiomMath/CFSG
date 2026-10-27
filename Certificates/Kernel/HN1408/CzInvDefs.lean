module

public import Certificates.Kernel.HN1408.CzTScanDefs
public import Certificates.Kernel.HN1408.CzInvData
public import Certificates.Kernel.HN1408.CzTDefs

public section

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT

@[expose] noncomputable def cjAt (A B H H' Q Q' x : Nat) : Bool :=
  Nat.beq (pt A (pt B (pt H (pt H' x)))) (pt H (pt H' (pt Q (pt Q' x))))

@[expose] noncomputable def conjK (R : Nat → Nat) (A B c₁ i' j' : Nat) : Bool :=
  strictB (R (Nat.pred c₁)) fun r => strictB (fd r 0) fun q => strictB (fd r 1) fun q' =>
    bAnd(Nat.blt i' 1280, bAnd(Nat.blt j' 24, bAnd(Nat.blt q 1280, bAnd(Nat.blt q' 24,
      strictB (T0 i') fun H => strictB (T1 j') fun H' => strictB (T0 q) fun Q =>
        strictB (T1 q') fun Q' => bAnd(cjAt A B H H' Q Q' 0, cjAt A B H H' Q Q' 1)))))

@[expose] noncomputable def cellK (R : Nat → Nat) (A B Wi j : Nat) : Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    strictB (fd Wi (Nat.mul 3 j)) fun c₁ =>
      bIf(bAnd(isBase (pt A (pt B g0)) (pt A (pt B g1)) 0 1, bIf(isBase g0 g1 0 1, false, true)),
        bIf(Nat.beq c₁ 0, false, bIf(Nat.blt 12 c₁, false,
          conjK R A B c₁ (fd Wi (Nat.add (Nat.mul 3 j) 1)) (fd Wi (Nat.add (Nat.mul 3 j) 2)))),
        Nat.beq c₁ 0)

@[expose] noncomputable def rowK (W R : Nat → Nat) (i : Nat) : Bool :=
  strictB (T0 i) fun A => strictB (W i) fun Wi => allN 24 fun j => cellK R A (T1 j) Wi j

@[expose] noncomputable def invSl (s : Nat) : Bool :=
  allN 64 fun d => rowK W R (Nat.add (Nat.mul 64 s) d)

@[expose] noncomputable def namedP (c : Nat) : Nat :=
  nIf(Nat.beq c 0, WK wordA, nIf(Nat.beq c 1, WK wordZ, nIf(Nat.beq c 2, pc (WK wordA) (WK wordZ),
    nIf(Nat.beq c 3, WK wordB, WK wordZ₁))))

@[expose] noncomputable def namedK (R : Nat → Nat) : Bool :=
  strictB (WK wordZ) fun Z => allN 5 fun c => strictB (namedP c) fun X => strictB (R c) fun r =>
    strictB (fd r 0) fun q => strictB (fd r 1) fun q' =>
      bAnd(Nat.blt q 1280, bAnd(Nat.blt q' 24, bAnd(commP X Z,
        strictB (T0 q) fun Q => strictB (T1 q') fun Q' =>
          isBase (pt Q (pt Q' 0)) (pt Q (pt Q' 1)) (pt X 0) (pt X 1))))

end CFSG.KD.HN1408.CzInv

end
