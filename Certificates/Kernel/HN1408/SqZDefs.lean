module

public import Certificates.Kernel.HN1408.CzInvDefs
public import Certificates.Kernel.HN1408.SqZData

public section

namespace CFSG.KD.HN1408.SqZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT

@[expose] def g1Word : List Nat := [4, 6, 5, 6, 7, 3, 5, 7, 1, 7, 2, 7, 1, 2, 6, 5, 5, 6, 4]

@[expose] def g1Cent : List (List Nat) :=
  [[4, 6, 5, 4, 6, 3, 5, 7, 2, 3, 2, 3, 3, 7, 5, 6, 5, 7, 3, 2, 1, 1, 6, 5, 1, 5, 6, 4],
    [4, 6, 5, 6, 5, 6, 1, 2, 1, 3, 7, 5, 6, 5, 7, 3, 2, 3, 2, 3, 6, 1, 2, 7, 3, 7, 5, 1, 7, 5, 6,
      4],
    [4, 6, 5, 1, 3, 4, 5, 7, 5, 6, 2, 3, 1, 3, 5, 7, 5, 6, 5, 7, 3, 1, 2, 5, 6, 4]]

@[expose] def h2Word : List Nat := [4, 3, 1, 6, 4, 2, 1]

@[expose] noncomputable def sqCellK (R : Nat → Nat) (A B Wi j : Nat) : Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    strictB (fd Wi (Nat.mul 3 j)) fun c₁ =>
      bIf(isBase (pt A (pt B g0)) (pt A (pt B g1)) 45 88,
        bIf(Nat.beq c₁ 0, false, bIf(Nat.blt 2 c₁, false,
          CzInv.conjK R A B c₁ (fd Wi (Nat.add (Nat.mul 3 j) 1)) (fd Wi (Nat.add (Nat.mul 3 j) 2)))),
        Nat.beq c₁ 0)

@[expose] noncomputable def sqRowK (W R : Nat → Nat) (i : Nat) : Bool :=
  strictB (T0 i) fun A => strictB (W i) fun Wi => allN 24 fun j => sqCellK R A (T1 j) Wi j

@[expose] noncomputable def sqSl (s : Nat) : Bool :=
  allN 64 fun d => sqRowK W R (Nat.add (Nat.mul 64 s) d)

@[expose] noncomputable def sqNamedK (R : Nat → Nat) : Bool :=
  strictB (WK wordA) fun Aa => strictB (WK g1Word) fun G1 => strictB (WK h2Word) fun H2 =>
    strictB (R 0) fun r => strictB (R 1) fun r' =>
      bAnd(Nat.beq (pt Aa 0) 45, bAnd(Nat.beq (pt Aa 1) 88, bAnd(Nat.beq (pc G1 G1) Aa,
        bAnd(Nat.blt (fd r 0) 1280, bAnd(Nat.blt (fd r 1) 24,
          bAnd(Nat.blt (fd r' 0) 1280, bAnd(Nat.blt (fd r' 1) 24,
            bAnd(Nat.beq (pc (T0 (fd r 0)) (T1 (fd r 1))) G1,
              Nat.beq (pc H2 (pc (T0 (fd r' 0)) (T1 (fd r' 1)))) (pc G1 H2)))))))))

end CFSG.KD.HN1408.SqZ

end
