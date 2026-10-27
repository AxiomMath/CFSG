module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSixInputs

public section

namespace CFSG.KD.LQT.Six4099

open Equiv Equiv.Perm CFSG.QuasithinUnique.Ch1.AltSix

@[expose] def epsTbl : List (List (Perm (Fin 6))) :=
  [[1, swap 0 1 * swap 2 4 * swap 3 5, swap 0 2 * swap 1 5 * swap 3 4,
      swap 0 3 * swap 1 2 * swap 4 5, swap 0 4 * swap 1 3 * swap 2 5,
      swap 0 5 * swap 1 4 * swap 2 3],
    [swap 0 1 * swap 2 4 * swap 3 5, 1, swap 0 3 * swap 1 4 * swap 2 5,
      swap 0 4 * swap 1 5 * swap 2 3, swap 0 5 * swap 1 2 * swap 3 4,
      swap 0 2 * swap 1 3 * swap 4 5],
    [swap 0 2 * swap 1 5 * swap 3 4, swap 0 3 * swap 1 4 * swap 2 5, 1,
      swap 0 5 * swap 1 3 * swap 2 4, swap 0 1 * swap 2 3 * swap 4 5,
      swap 0 4 * swap 1 2 * swap 3 5],
    [swap 0 3 * swap 1 2 * swap 4 5, swap 0 4 * swap 1 5 * swap 2 3,
      swap 0 5 * swap 1 3 * swap 2 4, 1, swap 0 2 * swap 1 4 * swap 3 5,
      swap 0 1 * swap 2 5 * swap 3 4],
    [swap 0 4 * swap 1 3 * swap 2 5, swap 0 5 * swap 1 2 * swap 3 4,
      swap 0 1 * swap 2 3 * swap 4 5, swap 0 2 * swap 1 4 * swap 3 5, 1,
      swap 0 3 * swap 1 5 * swap 2 4],
    [swap 0 5 * swap 1 4 * swap 2 3, swap 0 2 * swap 1 3 * swap 4 5,
      swap 0 4 * swap 1 2 * swap 3 5, swap 0 1 * swap 2 5 * swap 3 4,
      swap 0 3 * swap 1 5 * swap 2 4, 1]]

@[expose] def epsT (a b : Fin 6) : Perm (Fin 6) := (epsTbl.getD a.val []).getD b.val 1

@[expose] def pl : List (Fin 6) → List (Perm (Fin 6) × Perm (Fin 6) × Bool)
  | [] => [(1, 1, true)]
  | a :: l => pl l ++ l.flatMap fun b => (pl l).map fun p => (swap a b * p.1, epsT a b * p.2.1, !p.2.2)

@[expose] def L : List (Perm (Fin 6) × Perm (Fin 6) × Bool) := pl (List.finRange 6)

theorem epsT_ok : ∀ a b : Fin 6, a ≠ b → ∀ i, epsFun (swap a b) i = epsT a b i := by
  decide +kernel

theorem epsSq_ok : ∀ k : Fin 5, ∀ i, epsFun (epsT k.castSucc k.succ) i = swap k.castSucc k.succ i := by
  decide +kernel

theorem sign_ok : ∀ k : Fin 5, Perm.sign (epsT k.castSucc k.succ) = -1 := by
  decide +kernel

theorem supp3 : (epsT 0 1 * epsT 1 2).support.card = 6 := by
  decide +kernel

theorem central6 : ∀ τ : Perm (Fin 6), τ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * τ →
    τ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * τ →
    τ * (swap 2 3 * swap 3 4) = (swap 2 3 * swap 3 4) * τ →
    τ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * τ → τ = 1 := by
  decide +kernel

theorem clsTrue : L.all (fun p => !decide (p.1 * p.2.1 = 1) ||
    !decide (8 ∣ (L.filter fun q => q.2.2 && decide (p.1 * q.2.1 = q.1 * p.1)).length)) = true := by
  decide +kernel

theorem invTypes : L.all (fun p => !decide (p.1 * p.1 = 1) || decide (p.1 = 1) || p.2.2 ||
    decide (p.1.support.card = 2) || decide (p.2.1.support.card = 2)) = true := by
  decide +kernel

example : ¬ ∀ i, epsFun (swap 0 1) i = epsT 0 2 i := by decide +kernel

example : ¬ ∀ i, epsFun (epsT 0 1) i = swap 0 2 i := by decide +kernel

example : Perm.sign (epsT 0 1 * epsT 1 2) ≠ -1 := by decide +kernel

example : (epsT 0 1 * epsT 0 1).support.card ≠ 6 := by decide +kernel

example : ¬ ∀ τ : Perm (Fin 6), τ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * τ →
    τ * (swap 1 2 * swap 2 3) = (swap 1 2 * swap 2 3) * τ → τ = 1 :=
  fun h => absurd (h (swap 4 5) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

example : L.all (fun p => !decide (p.1 * p.2.1 = 1) ||
    !decide (10 ∣ (L.filter fun q => q.2.2 && decide (p.1 * q.2.1 = q.1 * p.1)).length)) = false := by
  decide +kernel

example : L.all (fun p => !decide (p.1 * p.1 = 1) || decide (p.1 = 1) || p.2.2 ||
    decide (p.1.support.card = 2)) = false := by
  decide +kernel

end CFSG.KD.LQT.Six4099
