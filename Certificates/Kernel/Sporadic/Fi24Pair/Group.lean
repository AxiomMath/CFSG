module

public import Certificates.Kernel.Sporadic.Fi24Pair.Facts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24PairOrbitFacts

public section

namespace CFSG.KD.Fi24Pair.Group

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J cls lvl gs letters)
open CFSG.Perm CFSG.KS.Fi24Net CFSG.KS.Fi24Kit CFSG.KC.Fi24Kit CFSG.KC.Fi24Pair

attribute [local instance] CFSG.Sporadic.Fi24.rAction


section Facts

variable
  (hL : ∀ l < 26, ∀ x : Fin 306936, ((pairG gs l) • x).val = LN CFSG.KD.Fi24Net.NW l x.val)
  (hC : ∀ k p : Fin 306936,
    (cls k • p).val = clsK CFSG.KD.Fi24Orb.OL CFSG.KD.Fi24Kit.NT k.val p.val)

include hL in
theorem word_val : ∀ (w : List ℕ), (∀ l ∈ w, l < 26) → ∀ x : Fin 306936,
    ((wordElt w) • x).val = wN CFSG.KD.Fi24Net.NW w x.val
  | [], _, x => by
    have e : wordElt [] = 1 := rfl
    rw [e, one_smul]
    rfl
  | l :: w, hw, x => by
    have e : wordElt (l :: w) = pairG gs l * wordElt w := by
      unfold wordElt
      rw [List.map_cons, List.prod_cons]
    rw [e, mul_smul, hL l (hw l List.mem_cons_self),
      word_val w (fun l' h => hw l' (List.mem_cons_of_mem l h)) x]
    rfl

include hL in
theorem c0_val : poC0.val = 254589 := by
  unfold poC0
  rw [word_val hL poW0 (by decide)]
  decide +kernel

include hL in
theorem c1_val : poC1.val = 61582 := by
  unfold poC1
  rw [word_val hL poW1 (by decide)]
  decide +kernel

include hL in
theorem h_val (x : Fin 306936) :
    ((wordElt poH) • x).val = wN CFSG.KD.Fi24Net.NW poH x.val :=
  word_val hL poH (by decide) x

theorem lvl_two_eq (hlv : CFSG.Perm.Native.levelLetters letters
    CFSG.Sporadic.Fi24.Native.chainBase 2 =
      #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
    lvl 2 = letH (fun k => pairG gs (8 + k)) := by
  unfold lvl CFSG.Perm.levelGroup CFSG.Perm.lettersGroup letH
  rw [hlv]
  congr 1
  ext g
  constructor
  · rintro ⟨l, hl, rfl⟩
    have h : 8 ≤ l ∧ l < 26 := by
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
      omega
    refine ⟨⟨l - 8, by omega⟩, ?_⟩
    change pairG gs (8 + (l - 8)) = pairG gs l
    congr 1
    omega
  · rintro ⟨k, rfl⟩
    refine ⟨8 + k.val, ?_, rfl⟩
    have := k.isLt
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
    omega

include hL hC in
theorem lam_mem {a : Fin 306936} (ha : PoLam a) :
    (((wordElt poH) • a).val, ((wordElt poH) • (poX • a)).val) ∈
      (List.range 6).map fun j => ((outP j).1, (outP j).2.2.1) := by
  unfold poX
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [h_val hL, mul_smul, hC, c0_val hL, c1_val hL, poP0, poP1] <;>
    decide +kernel

include hL hC in
theorem fi24PairOrbitFacts_of (hlv : CFSG.Perm.Native.levelLetters letters
    CFSG.Sporadic.Fi24.Native.chainBase 2 =
      #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
    Fi24PairOrbitFacts := by
  have hg : ∀ k < 18, ∀ x : Fin 306936,
      ((pairG gs (8 + k)) • x).val = LN CFSG.KD.Fi24Net.NW (8 + k) x.val :=
    fun k hk x => hL (8 + k) (by omega) x
  have key := pair_orbit (G := J) (fun k => pairG gs (8 + k)) hg poC0 poC1 (c0_val hL)
    (c1_val hL)
  have e := lvl_two_eq hlv
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    rw [h_val hL, c0_val hL]
    decide +kernel
  · apply Fin.ext
    rw [h_val hL, c1_val hL]
    decide +kernel
  · rw [e]
    exact key.1
  · intro a ha k hk ⟨e1, e2⟩
    rw [e] at hk
    obtain ⟨j, hj, hjeq⟩ := List.mem_map.1 (lam_mem hL hC ha)
    rw [Prod.ext_iff] at hjeq
    refine key.2 j (List.mem_range.1 hj) k hk ⟨?_, ?_⟩
    · rw [e1]
      exact hjeq.1.symm
    · rw [e2]
      exact hjeq.2.symm

end Facts

end CFSG.KD.Fi24Pair.Group

end
