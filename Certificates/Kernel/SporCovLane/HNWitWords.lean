module

public import CFSG.Sporadic.HNSchreier.Data
public import CFSG.Sporadic.HNSchreier.LocalData
public import CFSG.Sporadic.HNSchreier.FAData
public import Mathlib.Init

public section

namespace CFSG.KD.SporCovLane.HNWit

open CFSG.Sporadic.HNSchreier

@[expose] def pInit (r : Nat) : Nat × Nat :=
  if r = 1 then (0, 1) else if r = 2 then (2, 3) else (4, 4)

@[expose] def upd (σ : Nat → Nat × Nat) (c : Nat) (v : Nat × Nat) (r : Nat) : Nat × Nat :=
  if r = c then v else σ r

@[expose] def progW : (Nat → Nat × Nat) → Nat → List (Nat × Nat × Nat) → List (List Nat)
  | _, _, [] => []
  | σ, n, (a, b, c) :: rest =>
    [(σ b).1, (σ a).1] :: [(σ a).2, (σ b).2] :: progW (upd σ c (4 + n, 5 + n)) (n + 2) rest

@[expose] def progP : (Nat → Nat × Nat) → Nat → List (Nat × Nat × Nat) → Nat → Nat × Nat
  | σ, _, [] => σ
  | σ, n, (_, _, c) :: rest => progP (upd σ c (4 + n, 5 + n)) (n + 2) rest

@[expose] def sgnL (H : Nat → Nat × Nat) (l : Int) : Nat :=
  if 0 < l then (H (l.natAbs - 1)).1 else (H (l.natAbs - 1)).2

@[expose] def sgnLi (H : Nat → Nat × Nat) (l : Int) : Nat :=
  if 0 < l then (H (l.natAbs - 1)).2 else (H (l.natAbs - 1)).1

@[expose] def kwS (H : Nat → Nat × Nat) (w : List Int) : List Nat := (w.map (sgnL H)).reverse

@[expose] def kwSi (H : Nat → Nat × Nat) (w : List Int) : List Nat := w.map (sgnLi H)

@[expose] def strongW : (Nat → Nat × Nat) → Nat → Nat → List (List Int) → List (List Nat)
  | _, _, _, [] => []
  | H, j, n, w :: rest =>
    kwS H w :: kwSi H w :: strongW (upd H j (4 + n, 5 + n)) (j + 1) (n + 2) rest

@[expose] def strongP : (Nat → Nat × Nat) → Nat → Nat → List (List Int) → Nat → Nat × Nat
  | H, _, _, [] => H
  | H, j, n, _ :: rest => strongP (upd H j (4 + n, 5 + n)) (j + 1) (n + 2) rest

@[expose] def Pp : Nat → Nat × Nat := progP pInit 1 Data.subgroupProgram

@[expose] def H0 (j : Nat) : Nat × Nat := if j = 0 then Pp 1 else Pp 2

@[expose] def sw : List (List Int) := LocalData.strongWords.toList.drop 2

@[expose] def Hp : Nat → Nat × Nat := strongP H0 2 21 sw

@[expose] def g3W : List Nat :=
  kwS Hp FAData.g3H ++ (FAData.g3Root.map fun l => if l = 1 then 0 else 2).reverse

@[expose] def Ws : List (List Nat) :=
  [[]] ++ progW pInit 1 Data.subgroupProgram ++ strongW H0 2 21 sw ++
    [kwS Hp FAData.c3Words[0]!, g3W, [56, 56, 56, 56, 56, 56]]

abbrev C : Nat := 55

abbrev U : Nat := 57

end CFSG.KD.SporCovLane.HNWit

end
