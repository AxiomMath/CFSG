module

public import Certificates.Data.Kernel.M23AutK
public import Certificates.Kernel.M23Aut.Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.M23Aut

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.M23Aut

@[expose] noncomputable def tabA : List Nat :=
  [1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] noncomputable def tabB : List Nat :=
  [15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] noncomputable def ksW : List (List Nat) :=
  [[3, 2, 3, 2, 3, 3, 3, 2, 3, 2, 3, 3, 3, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [3, 3, 2, 3, 3, 2, 3, 2, 3, 3, 2, 3, 2, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [2, 3, 2, 3, 3, 3, 2, 3, 3, 3, 2, 3, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0]]

@[expose] noncomputable def genW : List (List Nat) :=
  [[4, 3, 4, 2, 0, 1, 4, 2, 0], [2, 1, 2, 4, 2, 0], [1, 4, 2, 0, 1, 4, 2, 0],
    [1, 0, 2, 1, 2, 1, 4, 1], [4, 1, 2, 4, 3, 2, 1, 3, 4], [3, 0]]

@[expose] noncomputable def lWW : List Nat := [1, 0, 1, 1, 0, 3]

@[expose] noncomputable def pW : List (List Nat) :=
  [[0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 1, 0],
    [2, 2, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1]]

@[expose] noncomputable def iW : List (List Nat) :=
  [[1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 1, 2, 1, 0, 0]]

@[expose] noncomputable def iWT : List (List Nat × Nat) :=
  iW.map fun w => (w, evK 23 e (withInv 23 [hA, hB]) w)

theorem ch7108_ab : andB (Nat.beq e (one 23))
    (andB (Nat.beq ta (ofFn 23 (nth tabA))) (Nat.beq tb (ofFn 23 (nth tabB)))) = true := by
  decide +kernel

theorem ch7108_ks : eqLK ks (ksW.map (evK 23 e (withInv 23 [ta, tb]))) = true := by
  decide +kernel

theorem ch7108_gens : eqLK [hA, hB, fA, fB, fC] ((genW.take 5).map (evK 23 e (withInv 23 ks))) = true ∧
    andB (Nat.beq lW (evK 23 e (withInv 23 [ta, tb]) lWW))
      (Nat.beq lX (mul 23 (mul 23 lW (evK 23 e (withInv 23 ks) [3, 0])) (inv 23 lW))) = true := by
  decide +kernel

theorem ch7108_mem : andB (andB (inHbarK hA) (inHbarK hB))
    (andB (andB (ord8K 23 e hA) (andB (ord2K 23 e hB) (ord5K 23 e (mul 23 hA hB))))
      (andB (pwK 23 e (withInv 23 [hA, hB]) pW)
        (andB (allL (iWT.map Prod.snd) inIxK)
          (andB (andB (inF4K fA) (andB (inF4K fB) (inF4K fC)))
            (andB (fixK lX [19, 21, 22]) (ord3K 23 e lX)))))) = true := by
  decide +kernel

theorem ch7108_sizes : hN = 1920 ∧ iN = 192 ∧ lN = 960 := ⟨rfl, rfl, rfl⟩

theorem ch7108_htree : treeK 23 e hN [hA, hB] hT hP hG hD = true := by decide +kernel

theorem ch7108_itree : treeK 23 e iN (iWT.map Prod.snd) iT iP iG iD = true := by decide +kernel

theorem ch7108_ltree : treeK 23 e lN [fA, fB, fC, lX] lT lP lG lD = true := by decide +kernel

theorem ch7108_ix : cntN hN (fun i => inIxK (tC 23 hT i)) = 192 := by decide +kernel

theorem ch7108_inv : CFSG.KC.Enum.allN hN (invAt 23 e hT i2) = true := by decide +kernel

theorem ch7108_orb : CFSG.KC.Enum.allN hN (orbAt 23 e hN 19 hT oC oR reps) = true := by
  decide +kernel

theorem ch7108_scan : scanK 23 e hN 19 hT i2 pW iWT reps = true := by decide +kernel

theorem ch7108_aut : andB (CFSG.KC.Enum.allN lN (autAt 23 e lT lX fw)) (fwOK 23 lN lT lX fw) =
    true := by
  decide +kernel

end CFSG.KD.M23Aut

end
