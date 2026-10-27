module

public import Certificates.Kernel.HN1408.CzTData
public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ClassData

public section

namespace CFSG.KD.HN1408.CzT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def n0 : Nat := 1280

@[expose] noncomputable def n1 : Nat := 24

@[expose] noncomputable def nS : Nat := 2

@[expose] noncomputable def fd (W i : Nat) : Nat := Nat.land (Nat.shiftRight W (Nat.mul 16 i)) 65535

@[expose] noncomputable def headK (G T0 T1 : Nat → Nat) : Bool :=
  bAnd(allN 2 (fun l => Nat.beq (G l) (WK (classz.centGens.getD l []))),
    bAnd(strictB (WK wordZ) (fun Z => allN 2 (fun l => commP (G l) Z)),
      bAnd(Nat.beq (T0 0) idK, Nat.beq (T1 0) idK)))

@[expose] noncomputable def keysK (T0 : Nat → Nat) : Bool :=
  allN (Nat.sub n0 1) fun i => Nat.blt (pt (T0 i) 0) (pt (T0 (Nat.succ i)) 0)

@[expose] noncomputable def treeK (G T0 P0 : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.beq i 0, true,
    strictB (P0 i) fun w => strictB (fd w 0) fun p => strictB (fd w 1) fun l =>
      bAnd(Nat.blt p n0, bAnd(Nat.blt l 2, bAnd(Nat.beq (fd w 2) (Nat.succ (fd (P0 p) 2)),
        Nat.beq (T0 i) (pc (G l) (T0 p))))))

@[expose] noncomputable def treeSl (s : Nat) : Bool :=
  allN 64 fun d => treeK G T0 P0 (Nat.add (Nat.mul 64 s) d)

@[expose] noncomputable def schK (G T0 S SR : Nat → Nat) (r : Nat) : Bool :=
  strictB (S r) fun X => strictB (SR r) fun w =>
    strictB (fd w 0) fun p => strictB (fd w 1) fun q => strictB (fd w 2) fun l =>
      bAnd(canonK 1408 11 (mask 11) (1408 * 11) X, bAnd(Nat.blt p n0, bAnd(Nat.blt q n0,
        bAnd(Nat.blt l 2, Nat.beq (pc (T0 q) X) (pc (G l) (T0 p))))))

@[expose] noncomputable def t1K (S T1 P1 : Nat → Nat) (j : Nat) : Bool :=
  strictB (T1 j) fun X => strictB (pt X 1) fun y =>
    bAnd(Nat.beq (pt X 0) 0,
      bAnd(allN j (fun j' => bIf(Nat.beq y (pt (T1 j') 1), false, true)),
        bIf(Nat.beq j 0, true,
          strictB (P1 j) fun w => strictB (fd w 0) fun p => strictB (fd w 1) fun r =>
            bAnd(Nat.blt p j, bAnd(Nat.blt r nS, Nat.beq X (pc (S r) (T1 p)))))))

end CFSG.KD.HN1408.CzT

end
