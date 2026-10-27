module

public import Certificates.Kernel.HN1408.CzTScanDefs
public import Certificates.Kernel.HN1408.CzInvData
public import Certificates.Kernel.HN1408.XCentData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XModelData
public import Certificates.Kernel.HN1408.CzTDefs

public section

namespace CFSG.KD.HN1408.XCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

@[expose] noncomputable def fd2 (W k : Nat) : Nat := Nat.land (Nat.shiftRight W (Nat.mul 2 k)) 3

@[expose] noncomputable def sub2 (X₁ X₂ i : Nat) : Nat :=
  nIf(Nat.beq i 1, X₁, nIf(Nat.beq i 2, X₂, idK))

@[expose] noncomputable def pwK (X₁ X₂ W : Nat) : Nat :=
  foldN 24 (fun k acc => pc (sub2 X₁ X₂ (fd2 W k)) acc) idK

@[expose] noncomputable def xcHead : Bool :=
  strictB (WK wordZ) fun Z => strictB (CT 0) fun C₁ => strictB (CT 1) fun C₂ =>
    bAnd(Nat.beq C₁ (WK xC1), bAnd(Nat.beq C₂ (WK xC2), bAnd(commP C₁ Z, commP C₂ Z)))

@[expose] noncomputable def xcWords (Et : Nat → Nat) : Bool :=
  strictB (CT 0) fun C₁ => strictB (CT 1) fun C₂ =>
    allN 46 fun k => Nat.beq (Et k) (pwK C₁ C₂ (Wd k))

@[expose] noncomputable def xcCenter (Et : Nat → Nat) : Bool :=
  strictB (CT 0) fun C₁ => strictB (CT 1) fun C₂ =>
    allN 8 fun k => bAnd(commP (Et k) C₁, commP (Et k) C₂)

@[expose] noncomputable def xcNorm (Et : Nat → Nat) : Bool :=
  allN 2 fun l => strictB (G l) fun U => allN 2 fun k => strictB (CT k) fun C =>
    strictB (Nat.add 8 (Nat.add (Nat.mul 4 l) (Nat.mul 2 k))) fun n =>
      bAnd(Nat.beq (pc U C) (pc (Et n) U), Nat.beq (pc C U) (pc U (Et (Nat.succ n))))

@[expose] noncomputable def good (r : Nat) : Nat :=
  nIf(Nat.beq r 0, 3, nIf(Nat.beq r 1, 4, nIf(Nat.beq r 2, 5, nIf(Nat.beq r 3, 6,
    nIf(Nat.beq r 4, 9, 10)))))

@[expose] noncomputable def bad (r : Nat) : Nat :=
  nIf(Nat.beq r 0, 0, nIf(Nat.beq r 1, 1, nIf(Nat.beq r 2, 2, nIf(Nat.beq r 3, 7,
    nIf(Nat.beq r 4, 8, 11)))))

@[expose] noncomputable def badN (r : Nat) : Nat :=
  nIf(Nat.blt r 3, 30720, nIf(Nat.beq r 4, 64, 1024))

@[expose] noncomputable def repT (Rc : Nat → Nat) (c : Nat) : Nat :=
  strictN (Rc c) fun r => pc (T0 (fd r 0)) (T1 (fd r 1))

@[expose] noncomputable def xcGood (Et Rc : Nat → Nat) (r : Nat) : Bool :=
  strictB (repT Rc (good r)) fun R => strictB (Nat.add 16 (Nat.mul 5 r)) fun b =>
    bAnd(commP (Et b) R, bAnd(commP (Et (Nat.add b 1)) R, bAnd(commP (Et (Nat.add b 2)) R,
      bAnd(commP (pc (G 0) (Et (Nat.add b 3))) R, commP (pc (G 1) (Et (Nat.add b 4))) R))))

@[expose] noncomputable def inZ (Et : Nat → Nat) (R g0 g1 : Nat) : Bool :=
  !(allN 8 fun k => strictB (Et k) fun Zk =>
    !(bIf(isBase g0 g1 (pt Zk 0) (pt Zk 1), true, isBase g0 g1 (pt Zk (pt R 0)) (pt Zk (pt R 1)))))

@[expose] noncomputable def cutRow (Et : Nat → Nat) (K₀ K₁ K₂ R A B : Nat) : Bool :=
  strictB (pt A (pt B 0)) fun g0 => strictB (pt A (pt B 1)) fun g1 =>
    bIf(bAnd(commB A B K₀ g0 g1, bAnd(commB A B K₁ g0 g1, commB A B K₂ g0 g1)),
      inZ Et R g0 g1, true)

@[expose] noncomputable def xcScan (Et Rc : Nat → Nat) (r : Nat) : Bool :=
  strictB (repT Rc (good r)) fun R => strictB (Nat.add 16 (Nat.mul 5 r)) fun b =>
    strictB (Et b) fun K₀ => strictB (Et (Nat.add b 1)) fun K₁ =>
      strictB (Et (Nat.add b 2)) fun K₂ => czScan T0 T1 (cutRow Et K₀ K₁ K₂ R)

@[expose] noncomputable def cntRow (R A s : Nat) : Nat :=
  foldN 24 (fun j s => strictN (T1 j) fun B =>
    nIf(commB A B R (pt A (pt B 0)) (pt A (pt B 1)), Nat.succ s, s)) s

@[expose] noncomputable def cntC (R : Nat) : Nat :=
  foldN 1280 (fun i s => strictN (T0 i) fun A => cntRow R A s) 0

@[expose] noncomputable def xcCnt (Rc : Nat → Nat) (r : Nat) : Bool :=
  Nat.beq (cntC (repT Rc (bad r))) (badN r)

@[expose] noncomputable def goodD (r : Nat) : Bool := xcGood E CzInv.R r

@[expose] noncomputable def scanD (r : Nat) : Bool := xcScan E CzInv.R r

@[expose] noncomputable def cntD (r : Nat) : Bool := xcCnt CzInv.R r

end CFSG.KD.HN1408.XCent

end
