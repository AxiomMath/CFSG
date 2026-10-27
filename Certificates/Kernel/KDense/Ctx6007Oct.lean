module

public import Certificates.Data.CFSGNative.MonsterAxis.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelKDense

open CFSG.Monster.AxisCount.Native CFSG.Monster.B.Rep4371.Native

theorem popcN_eq_card : ∀ k a, popcN k a = ((Finset.range k).filter fun i => a.testBit i = true).card
  | 0, _ => rfl
  | k + 1, a => by
    rw [popcN, popcN_eq_card k, Finset.card_filter, Finset.card_filter, Finset.sum_range_succ',
      Nat.testBit_zero]
    simp only [Nat.testBit_succ]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h, add_comm]

theorem combN_lt_two_pow {m : Nat → Nat} {n i : Nat} (a : Nat) (hm : ∀ j < n, m j < 2 ^ i) :
    combN m n a < 2 ^ i := by
  induction n with
  | zero => exact Nat.two_pow_pos i
  | succ n ih =>
    rw [combN]
    refine Nat.xor_lt_two_pow (ih fun j hj => hm j (Nat.lt_succ_of_lt hj)) ?_
    split_ifs
    · exact hm n (Nat.lt_succ_self n)
    · exact Nat.two_pow_pos i

theorem wordN_lt (a : Nat) : wordN a < 2 ^ 24 :=
  combN_lt_two_pow a fun j hj => by interval_cases j <;> decide

theorem testBit_combN_pow {p : Nat → Nat} {n : Nat} (hp : ∀ s < n, ∀ t < n, p s = p t → s = t)
    (m i : Nat) :
    (combN (fun t => 2 ^ p t) n m).testBit i = true ↔ ∃ t < n, p t = i ∧ m.testBit t = true := by
  induction n with
  | zero => simp [combN]
  | succ n ih =>
    have ih := ih fun s hs t ht h => hp s (Nat.lt_succ_of_lt hs) t (Nat.lt_succ_of_lt ht) h
    rw [combN, Nat.testBit_xor]
    by_cases hi : p n = i
    · subst hi
      have h0 : (combN (fun t => 2 ^ p t) n m).testBit (p n) = false := by
        rw [Bool.eq_false_iff]
        intro h
        obtain ⟨t, ht, hpt, -⟩ := ih.1 h
        exact absurd (hp t (Nat.lt_succ_of_lt ht) n (Nat.lt_succ_self n) hpt) (Nat.ne_of_lt ht)
      rw [h0, Bool.false_xor]
      constructor
      · intro h
        refine ⟨n, Nat.lt_succ_self n, rfl, ?_⟩
        by_contra hb
        simp [hb] at h
      · rintro ⟨t, ht, hpt, hmt⟩
        obtain rfl := hp t ht n (Nat.lt_succ_self n) hpt
        simp [hmt]
    · have h0 : (if m.testBit n = true then 2 ^ p n else 0).testBit i = false := by
        split_ifs
        · rw [Nat.testBit_two_pow]
          simp [hi]
        · exact Nat.zero_testBit i
      rw [h0, Bool.xor_false, ih]
      constructor
      · rintro ⟨t, ht, h⟩
        exact ⟨t, Nat.lt_succ_of_lt ht, h⟩
      · rintro ⟨t, ht, hpt, hmt⟩
        refine ⟨t, ?_, hpt, hmt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h | rfl
        · exact h
        · exact absurd hpt hi

section Octad

variable {w : Nat}

theorem mem_suppList {i : Nat} : i ∈ suppList w ↔ i < 24 ∧ w.testBit i = true := by
  simp [suppList]

theorem nodup_suppList : (suppList w).Nodup := List.nodup_range.filter _

theorem length_suppList : (suppList w).length = popcN 24 w := by
  rw [popcN_eq_card, ← List.toFinset_card_of_nodup nodup_suppList]
  congr 1
  ext i
  simp [mem_suppList]

variable (hw : w < 2 ^ 24) (h8 : popcN 24 w = 8)
include h8

theorem getD_suppList {t : Nat} (ht : t < 8) :
    (suppList w).getD t 0 = (suppList w)[t]'(by rw [length_suppList, h8]; exact ht) :=
  by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

theorem getD_suppList_mem {t : Nat} (ht : t < 8) : (suppList w).getD t 0 ∈ suppList w := by
  rw [getD_suppList h8 ht]
  exact List.getElem_mem _

theorem getD_suppList_inj : ∀ s < 8, ∀ t < 8,
    (suppList w).getD s 0 = (suppList w).getD t 0 → s = t := by
  intro s hs t ht h
  rw [getD_suppList h8 hs, getD_suppList h8 ht] at h
  exact (nodup_suppList.getElem_inj_iff).1 h

theorem exists_getD_suppList {i : Nat} (hi : w.testBit i = true) (hlt : w < 2 ^ 24) :
    ∃ t < 8, (suppList w).getD t 0 = i := by
  have h24 : i < 24 := by
    by_contra h
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_of_not_lt h)))] at hi
    exact Bool.false_ne_true hi
  obtain ⟨t, ht, hti⟩ := List.mem_iff_getElem.1 (mem_suppList.2 ⟨h24, hi⟩)
  have ht8 : t < 8 := by rwa [length_suppList, h8] at ht
  exact ⟨t, ht8, by rw [getD_suppList h8 ht8]; exact hti⟩

theorem testBit_spreadG (m i : Nat) :
    (spreadG w m).testBit i = true ↔
      ∃ t < 8, (suppList w).getD t 0 = i ∧ m.testBit t = true :=
  testBit_combN_pow (getD_suppList_inj h8) m i

theorem testBit_spreadG_supp (m : Nat) {t : Nat} (ht : t < 8) :
    (spreadG w m).testBit ((suppList w).getD t 0) = m.testBit t := by
  rw [Bool.eq_iff_iff, testBit_spreadG h8]
  constructor
  · rintro ⟨s, hs, hst, hms⟩
    rwa [← getD_suppList_inj h8 s hs t ht hst]
  · intro h
    exact ⟨t, ht, rfl, h⟩

theorem testBit_spreadG_of_not {m i : Nat} (hi : w.testBit i = false) :
    (spreadG w m).testBit i = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨t, ht, rfl, -⟩ := (testBit_spreadG h8 m _).1 h
  rw [(mem_suppList.1 (getD_suppList_mem h8 ht)).2] at hi
  exact Bool.noConfusion hi

omit h8 in
theorem testBit_255 {t : Nat} (ht : t < 8) : (255 : Nat).testBit t = true := by
  interval_cases t <;> decide

include hw

theorem spreadG_parts :
    (∀ m, m < 256 →
      spreadG w m &&& w = spreadG w m ∧
      popcN 24 (spreadG w m) = popcN 8 m ∧
      spreadG w (m ^^^ 255) = spreadG w m ^^^ w) ∧
    (∀ m m', m < 256 → m' < 256 →
      spreadG w (m &&& m') = spreadG w m &&& spreadG w m' ∧
      (m = m' ∨ spreadG w m ≠ spreadG w m')) := by
  refine ⟨fun m hm => ⟨?_, ?_, ?_⟩, fun m m' hm hm' => ⟨?_, ?_⟩⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : w.testBit i
    · rw [testBit_spreadG_of_not h8 hi]
      rfl
    · rw [Bool.and_true]
  · rw [popcN_eq_card, popcN_eq_card]
    have himg : ((Finset.range 24).filter fun i => (spreadG w m).testBit i = true) =
        ((Finset.range 8).filter fun t => m.testBit t = true).image
          fun t => (suppList w).getD t 0 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨-, hi⟩
        obtain ⟨t, ht, rfl, hmt⟩ := (testBit_spreadG h8 m i).1 hi
        exact ⟨t, ⟨ht, hmt⟩, rfl⟩
      · rintro ⟨t, ⟨ht, hmt⟩, rfl⟩
        exact ⟨(mem_suppList.1 (getD_suppList_mem h8 ht)).1, (testBit_spreadG h8 m _).2
          ⟨t, ht, rfl, hmt⟩⟩
    rw [himg, Finset.card_image_of_injOn]
    intro s hs t ht hst
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hs ht
    exact getD_suppList_inj h8 s hs.1 t ht.1 hst
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor]
    cases hi : w.testBit i
    · rw [testBit_spreadG_of_not h8 hi, testBit_spreadG_of_not h8 hi]
      rfl
    · obtain ⟨t, ht, rfl⟩ := exists_getD_suppList h8 hi hw
      rw [testBit_spreadG_supp h8 _ ht, testBit_spreadG_supp h8 _ ht, Nat.testBit_xor,
        testBit_255 ht, Bool.xor_true]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : w.testBit i
    · rw [testBit_spreadG_of_not h8 hi, testBit_spreadG_of_not h8 hi]
      rfl
    · obtain ⟨t, ht, rfl⟩ := exists_getD_suppList h8 hi hw
      rw [testBit_spreadG_supp h8 _ ht, testBit_spreadG_supp h8 _ ht, testBit_spreadG_supp h8 _ ht,
        Nat.testBit_and]
  · by_cases h : spreadG w m = spreadG w m'
    · left
      apply Nat.eq_of_testBit_eq
      intro t
      by_cases ht : t < 8
      · rw [← testBit_spreadG_supp h8 m ht, ← testBit_spreadG_supp h8 m' ht, h]
      · have h256 : 256 ≤ 2 ^ t :=
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt ht) : 2 ^ 8 ≤ 2 ^ t)
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm h256),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hm' h256)]
    · exact Or.inr h

end Octad

end CertificateChecks.KernelKDense

end
