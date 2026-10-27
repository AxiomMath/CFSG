module

public import Certificates.Kernel.HN1408.CzTScanDefs
public import Certificates.Kernel.HN1408.SylTDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData
public import Certificates.Kernel.HN1408.CzTData

public section

namespace CFSG.KD.HN1408.AK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.KD.HN1408.CzT

@[expose] noncomputable def U (i : Nat) : Nat := WK (uWords.getD i [])

@[expose] noncomputable def anyK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k ih => bIf(f k, true, ih)) n

@[expose] noncomputable def bt (k i : Nat) : Nat := Nat.land (Nat.shiftRight k i) 1

@[expose] noncomputable def itK (X0 X1 X2 X3 X4 X5 k : Nat) : Nat :=
  strictN (nIf(Nat.beq (bt k 5) 1, X5, idK)) fun a5 =>
  strictN (nIf(Nat.beq (bt k 4) 1, pc X4 a5, a5)) fun a4 =>
  strictN (nIf(Nat.beq (bt k 3) 1, pc X3 a4, a4)) fun a3 =>
  strictN (nIf(Nat.beq (bt k 2) 1, pc X2 a3, a3)) fun a2 =>
  strictN (nIf(Nat.beq (bt k 1) 1, pc X1 a2, a2)) fun a1 =>
    nIf(Nat.beq (bt k 0) 1, pc X0 a1, a1)

@[expose] noncomputable def itP (X0 X1 X2 X3 X4 X5 k x : Nat) : Nat :=
  strictN (nIf(Nat.beq (bt k 5) 1, pt X5 x, x)) fun y5 =>
  strictN (nIf(Nat.beq (bt k 4) 1, pt X4 y5, y5)) fun y4 =>
  strictN (nIf(Nat.beq (bt k 3) 1, pt X3 y4, y4)) fun y3 =>
  strictN (nIf(Nat.beq (bt k 2) 1, pt X2 y3, y3)) fun y2 =>
  strictN (nIf(Nat.beq (bt k 1) 1, pt X1 y2, y2)) fun y1 =>
    nIf(Nat.beq (bt k 0) 1, pt X0 y1, y1)

@[expose] noncomputable def basicB (X0 X1 X2 X3 X4 X5 Z1 : Nat) : Bool :=
  bAnd(involK X0, bAnd(involK X1, bAnd(involK X2, bAnd(involK X3, bAnd(involK X4, bAnd(involK X5,
  bAnd(commP X0 X1, bAnd(commP X0 X2, bAnd(commP X0 X3, bAnd(commP X0 X4, bAnd(commP X0 X5,
  bAnd(commP X1 X2, bAnd(commP X1 X3, bAnd(commP X1 X4, bAnd(commP X1 X5,
  bAnd(commP X2 X3, bAnd(commP X2 X4, bAnd(commP X2 X5,
  bAnd(commP X3 X4, bAnd(commP X3 X5, bAnd(commP X4 X5,
  bAnd(Nat.beq (pc X0 (pc X2 (pc X3 X5))) Z1,
    allN 63 fun k => bIf(Nat.beq (itP X0 X1 X2 X3 X4 X5 (Nat.succ k) 0) 0,
      bIf(Nat.beq (itP X0 X1 X2 X3 X4 X5 (Nat.succ k) 1) 1, false, true), true)))))))))))))))))))))))

@[expose] noncomputable def basicK : Bool :=
  strictB (U 0) fun X0 => strictB (U 1) fun X1 => strictB (U 2) fun X2 => strictB (U 3) fun X3 =>
    strictB (U 4) fun X4 => strictB (U 5) fun X5 => basicB X0 X1 X2 X3 X4 X5 (WK wordZ₁)

@[expose] noncomputable def halfK : Bool :=
  bAnd(allN 5 fun i => halvesK (U i), Nat.ble 704 (pt (U 5) 0))

@[expose] noncomputable def genBlkPK : Bool := allN 7 fun j => SylT.blkGenK (WK [Nat.succ j])

@[expose] noncomputable def centRow (X0 X1 X2 X3 X4 X5 A B : Nat) : Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    bIf(bAnd(commB A B X1 g0 g1, bAnd(commB A B X2 g0 g1, bAnd(commB A B X3 g0 g1,
        commB A B X5 g0 g1))),
      anyK 64 (fun k => isBase g0 g1 (itP X0 X1 X2 X3 X4 X5 k 0) (itP X0 X1 X2 X3 X4 X5 k 1)),
      true)

@[expose] noncomputable def centK : Bool :=
  strictB (U 0) fun X0 => strictB (U 1) fun X1 => strictB (U 2) fun X2 => strictB (U 3) fun X3 =>
    strictB (U 4) fun X4 => strictB (U 5) fun X5 => czScan T0 T1 (centRow X0 X1 X2 X3 X4 X5)

@[expose] def aCode : List Nat :=
  [1, 2, 28, 4, 16, 52, 30, 4, 23, 5, 16, 33, 23, 2, 4, 30, 16, 38]

@[expose] noncomputable def normB (X0 X1 X2 X3 X4 X5 G l : Nat) : Bool :=
  bAnd(Nat.beq (pc G X0) (pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l) 0)) G),
  bAnd(Nat.beq (pc G X1) (pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l + 1) 0)) G),
  bAnd(Nat.beq (pc G X2) (pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l + 2) 0)) G),
  bAnd(Nat.beq (pc G X3) (pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l + 3) 0)) G),
  bAnd(Nat.beq (pc G X4) (pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l + 4) 0)) G),
    Nat.beq (pc G X5) (pc (itK X0 X1 X2 X3 X4 X5 (aCode.getD (6 * l + 5) 0)) G))))))

@[expose] noncomputable def normK : Bool :=
  strictB (U 0) fun X0 => strictB (U 1) fun X1 => strictB (U 2) fun X2 => strictB (U 3) fun X3 =>
    strictB (U 4) fun X4 => strictB (U 5) fun X5 =>
      allN 3 fun l => strictB (WK (normGens.getD l [])) fun G => normB X0 X1 X2 X3 X4 X5 G l

@[expose] noncomputable def mapC (l k : Nat) : Nat :=
  (List.range 6).foldr (fun i acc => nIf(Nat.beq (bt k i) 1, Nat.xor (aCode.getD (6 * l + i) 0) acc,
    acc)) 0

@[expose] def aTree : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (1, 0, 0), (28, 1, 4), (3, 0, 0), (8, 0, 3), (8, 1, 3), (30, 1, 2), (17, 2, 3),
    (30, 2, 2), (29, 0, 3), (30, 0, 2), (25, 1, 3), (26, 2, 2), (21, 0, 2), (22, 0, 3), (23, 0, 2),
    (0, 0, 0), (26, 1, 2), (12, 1, 3), (6, 1, 3), (24, 0, 4), (3, 2, 1), (26, 0, 2), (1, 2, 1),
    (12, 0, 3), (21, 1, 2), (3, 1, 1), (15, 0, 3), (10, 2, 3), (23, 1, 2), (1, 1, 1), (7, 0, 4),
    (32, 0, 0), (32, 1, 1), (58, 0, 4), (51, 2, 3), (40, 1, 4), (53, 2, 3), (32, 2, 1), (51, 0, 3),
    (56, 2, 3), (37, 0, 4), (38, 0, 2), (45, 2, 1), (39, 1, 4), (45, 0, 0), (62, 2, 3), (49, 1, 3),
    (40, 0, 4), (33, 2, 2), (52, 2, 2), (43, 0, 2), (32, 0, 1), (33, 0, 2), (48, 2, 5), (39, 2, 4),
    (52, 0, 2), (53, 0, 3), (42, 2, 3), (35, 1, 4), (44, 2, 5), (59, 2, 5), (43, 1, 2), (33, 1, 2)]

@[expose] noncomputable def fuseRow (T : List (Nat × Nat × Nat)) (k : Nat) : Bool :=
  let r := T.getD k (0, 0, 0)
  if r.2.2 = 0 then typeBase.getD (typeIdx k) 0 = k else
    decide (r.1 < 64) && r.1 != 0 && r.1 != 16 && decide (r.2.1 < 3) &&
      mapC r.2.1 r.1 == k && (T.getD r.1 (0, 0, 0)).2.2 + 1 == r.2.2 &&
      typeIdx r.1 == typeIdx k

@[expose] noncomputable def fuseKT (T : List (Nat × Nat × Nat)) : Bool :=
  (List.range 64).all fun k => k == 0 || k == 16 || fuseRow T k

@[expose] noncomputable def fuseK : Bool := fuseKT aTree

@[expose] noncomputable def fuseRelB (X0 X1 X2 X3 X4 X5 G0 G1 G2 k : Nat) : Bool :=
  bIf(Nat.beq (aTree.getD k (0, 0, 0)).2.2 0, true,
    strictB (nIf(Nat.beq (aTree.getD k (0, 0, 0)).2.1 0, G0,
      nIf(Nat.beq (aTree.getD k (0, 0, 0)).2.1 1, G1, G2))) fun G =>
      Nat.beq (pc G (itK X0 X1 X2 X3 X4 X5 (aTree.getD k (0, 0, 0)).1))
        (pc (itK X0 X1 X2 X3 X4 X5 k) G))

@[expose] noncomputable def fuseRelK : Bool :=
  strictB (U 0) fun X0 => strictB (U 1) fun X1 => strictB (U 2) fun X2 => strictB (U 3) fun X3 =>
    strictB (U 4) fun X4 => strictB (U 5) fun X5 => strictB (WK (normGens.getD 0 [])) fun G0 =>
      strictB (WK (normGens.getD 1 [])) fun G1 => strictB (WK (normGens.getD 2 [])) fun G2 =>
        allN 64 fun k => fuseRelB X0 X1 X2 X3 X4 X5 G0 G1 G2 k

end CFSG.KD.HN1408.AK

end
