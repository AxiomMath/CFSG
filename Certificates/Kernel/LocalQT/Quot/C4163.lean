module

public import Certificates.Kernel.LocalQT.Base.C4143D
public import Certificates.Data.Kernel.LocalQT.QuotS
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.LocalQT.Quot.G4163

public section

set_option maxRecDepth 100000

#kc_eval CFSG.KD.LQT.C4163 KG CFSG.KD.LQT.C4163.stepG

namespace CFSG.KD.LQT.C4163

open CFSG.KC.LQT.QS CFSG.KC.LQT.PW
open CFSG.KC.LQT.P (allL)
open CFSG.KLie.CT (notB)

@[expose] def mw2 : List Nat :=
  [1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0]

@[expose] def xs2 : List (List Nat × Nat × Nat) :=
  [([0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3, 3, 0, 3, 2, 1, 0, 2, 0], 4, 3),
   ([0, 1, 2, 0, 2, 3, 1, 2, 2, 3, 3, 0, 3, 1, 3, 3, 1, 2, 2, 0, 3, 0, 1, 3, 2, 3, 0, 3], 4, 3),
   ([2, 3, 1, 1, 1, 0, 1, 1, 3, 2, 2, 3, 2, 0, 3, 1], 2, 7)]

@[expose] def ws2 : List (List Nat) :=
  [[0, 4, 2, 4, 3, 5, 3, 5, 0], [0, 1, 2, 0, 5, 0, 5, 1], [2, 3, 2, 3, 5, 4, 5, 1],
    [5, 0, 4, 3, 1, 0, 2]]

@[expose] noncomputable def LC2 : List Nat :=
  [CFSG.KD.LQT.C4143.TF 163, CFSG.KD.LQT.C4143.TF 172, CFSG.KD.LQT.C4143.TF 185,
    wordC 4060 12 [CFSG.KD.LQT.C4143.TF 0, CFSG.KD.LQT.C4143.TF 1] mw2]

@[expose] noncomputable def gC (x : List Nat × Nat × Nat) : Nat :=
  powC 4060 12 (wordC 4060 12 LC2 x.1) x.2.1

theorem kGen : (Nat.beq KG.GC.length 6 &&
    allL [0, 1, 2] (fun i => Nat.beq (KG.GC.getD i 0) (gC (xs2.getD i ([], 0, 0)))) &&
    allL [0, 1, 2] (fun i => Nat.beq (KG.GC.getD (i + 3) 0)
      (powC 4060 12 (KG.GC.getD i 0) ((xs2.getD i ([], 0, 0)).2.2 - 1)))) = true := by
  quickRfl

theorem kOdd : allL [0, 1, 2] (fun i => Nat.beq
    (powC 4060 12 (KG.GC.getD i 0) (xs2.getD i ([], 0, 0)).2.2) (oneW 4060 12)) = true := by
  quickRfl

theorem kWords : allL [0, 1, 2, 3] (fun j => Nat.beq (wordC 4060 12 KG.GC (ws2.getD j []))
    (LC2.getD j 0)) = true := by quickRfl

theorem negOdd : notB (Nat.beq (powC 4060 12 (KG.GC.getD 2 0) 3) (oneW 4060 12)) = true := by
  quickRfl

theorem negWord : notB (Nat.beq (wordC 4060 12 KG.GC (ws2.getD 0 [])) (LC2.getD 1 0)) = true := by
  quickRfl

end CFSG.KD.LQT.C4163

end
