module

public import Certificates.Kernel.He.Words
public import CFSG.Certificates.Kernel.Ru.Bound.RelsTC
public import CFSG.Certificates.Kernel.Common.LceSRange
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelRu

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE TauCeti
open CertificateChecks.KernelHe

theorem wordNat_eq : ∀ w : List (ℕ × Bool), RuB.wordNat w = HeB.wordNat w
  | [] => rfl
  | l :: w => by
    rw [RuB.wordNat, HeB.wordNat, wordNat_eq w]
    rfl

theorem ent_eq (w : List (ℕ × Bool)) : RuB.ent w = HeB.ent w := by
  rw [RuB.ent, HeB.ent, wordNat_eq]

theorem letters_small : ∀ w ∈ Sporadic.ruPresentation.relatorLetters,
    w.length < 1024 ∧ ∀ l ∈ w, l.1 < 127 := by
  rw [Sporadic.ruPresentation_relatorLetters]
  decide

theorem rel_eq (r : ℕ) : RuB.rel r = RuB.list.getD r 0 := by
  rcases Nat.lt_or_ge r 12 with h | h
  · interval_cases r <;> rfl
  · have e : ∀ k < 12, Nat.beq r k = false := fun k hk =>
      Bool.eq_false_iff.mpr (fun hc => by rw [Nat.beq_eq] at hc; omega)
    simp only [RuB.rel, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega),
      e 9 (by omega), e 10 (by omega), e 11 (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [RuB.list]; omega)]
    rfl

theorem rel_ok (r : ℕ) :
    wWord (RuB.rel r) < 2 ^ (8 * wLen (RuB.rel r)) ∧
      bval (KB.tcGen Sporadic.ruPresentation) (wWord (RuB.rel r)) (wLen (RuB.rel r)) = 1 := by
  rw [rel_eq, ← RuB.relatorLetters_ent, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hw : Sporadic.ruPresentation.relatorLetters[r]? with _ | w
  · exact ⟨by decide, rfl⟩
  · have hmem := List.mem_of_getElem? hw
    obtain ⟨hlen, hl⟩ := letters_small w hmem
    simp only [Option.map_some, Option.getD_some, ent_eq]
    rw [wWord_ent w hlen, wLen_ent w hlen]
    exact ⟨wordNat_lt w hl, (bval_wordNat _ w hl).trans (KB.sword_relatorLetters _ w hmem)⟩

@[expose] noncomputable def qlet (W' W n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc
    (andB (Nat.blt (wLet W i) (nat_lit 4))
      (Nat.beq (wLet W' i) (Nat.add (wLet W i) (Nat.land (wLet W i) (nat_lit 2)))))) n

theorem andB_true_iff (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem qlet_sound {W' W : Nat} : ∀ {n}, qlet W' W n = true → ∀ i < n,
    wLet W i < 4 ∧ wLet W' i = wLet W i + (wLet W i &&& 2)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : andB (qlet W' W n) (andB (Nat.blt (wLet W n) 4)
        (Nat.beq (wLet W' n) (Nat.add (wLet W n) (Nat.land (wLet W n) 2)))) = true := h
    rw [andB_true_iff, andB_true_iff, Nat.blt_eq, Nat.beq_eq] at h'
    rcases Nat.lt_or_ge i n with hin | hin
    · exact qlet_sound h'.1 i hin
    · have : i = n := by omega
      subst this
      exact ⟨h'.2.1, h'.2.2⟩

theorem rec_andB_sound (f : Nat → Bool) : ∀ {n},
    Nat.rec (motive := fun _ => Bool) true (fun h ih => andB (f h) ih) n = true →
      ∀ h < n, f h = true
  | 0, _, h, hh => absurd hh (Nat.not_lt_zero h)
  | n + 1, hr, h, hh => by
    have hr' : andB (f n) (Nat.rec (motive := fun _ => Bool) true (fun h ih => andB (f h) ih) n) =
      true := hr
    rw [andB_true_iff] at hr'
    rcases Nat.lt_or_ge h n with hn | hn
    · exact rec_andB_sound f hr'.2 h hn
    · have : h = n := by omega
      subst this
      exact hr'.1

set_option maxRecDepth 20000 in
theorem wtPer0_sound {WT : Nat → Nat} {m P : Nat} (h : LceSR.wtPer0 WT m P = true) :
    ∀ k < 65536, WT k = 0 ∨ ∃ k' < m, WT k = WT k' := by
  intro k hk
  have hk1 : k / 256 < 256 := Nat.div_lt_of_lt_mul hk
  have hk2 : k % 256 < 256 := Nat.mod_lt k (by norm_num)
  let g : Nat → Bool := fun k => orB (Nat.beq (WT k) (nat_lit 0))
    (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))))
  let F : Nat → Bool := fun h => Nat.rec (motive := fun _ => Bool) true
    (fun l ih2 => andB (g (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2) (nat_lit 256)
  have h0 : Nat.rec (motive := fun _ => Bool) true (fun h ih => andB (F h) ih) (nat_lit 256) =
    true := h
  have h1 := rec_andB_sound F h0 (k / 256) hk1
  have h2 := rec_andB_sound (fun l => g (Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) l)) h1
    (k % 256) hk2
  have sl : Nat.shiftLeft (k / 256) (nat_lit 8) = k / 256 * 2 ^ 8 := Nat.shiftLeft_eq _ _
  have hk' : Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) (k % 256) = k := by
    rw [sl, Nat.add_eq]
    omega
  have h3 : g (Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) (k % 256)) = true := h2
  rw [hk'] at h3
  have h4 : orB (Nat.beq (WT k) 0)
      (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P)))) = true := h3
  cases hb : Nat.beq (WT k) 0
  · rw [hb] at h4
    have h5 : andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))) = true := h4
    rw [andB_true_iff, Nat.blt_eq, Nat.beq_eq] at h5
    exact Or.inr ⟨k % P, h5.1, h5.2⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true hb)

theorem bval_congr {G : Type*} [Group G] (g h : ℕ → G) {W V n : ℕ}
    (e : ∀ i < n, letV g (wLet W i) = letV h (wLet V i)) : bval g W n = bval h V n := by
  unfold bval
  congr 1
  apply List.map_congr_left
  intro i hi
  exact e i (List.mem_range.mp hi)

theorem card_le_step' {G : Type*} [Group G] {H K : Subgroup G} {N M : ℕ}
    (h : H.relIndex K ≠ 0 ∧ H.relIndex K ≤ N) (hH : Nat.card H ≠ 0 ∧ Nat.card H ≤ M) :
    Nat.card K ≠ 0 ∧ Nat.card K ≤ N * M := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero hH.1
  have hle : Nat.card (H ⊓ K : Subgroup G) ≤ Nat.card H := Subgroup.card_le_of_le inf_le_left
  have h0 : Nat.card (H ⊓ K : Subgroup G) ≠ 0 := by
    have : Finite (H ⊓ K : Subgroup G) := Finite.of_injective _
      (Subgroup.inclusion_injective (inf_le_left : H ⊓ K ≤ H))
    exact Nat.card_pos.ne'
  rw [← Subgroup.inf_relIndex_right] at h
  exact KB.card_le_step ⟨inf_le_right, h⟩ ⟨h0, hle.trans hH.2⟩

theorem card_klein_le {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) ≠ 0 ∧
      Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 4 := by
  classical
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hcomm : y * x = x * y := by
    have : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
    rw [mul_inv_rev, hxi, hyi] at this
    exact this
  have hxx : ∀ g, x * (x * g) = g := fun g => by rw [← mul_assoc, hx, one_mul]
  have hyx : ∀ g, y * (x * g) = x * (y * g) := fun g => by rw [← mul_assoc, hcomm, mul_assoc]
  let S : Finset G := {1, x, y, x * y}
  have hsub : (Subgroup.closure ({x, y} : Set G) : Set G) ⊆ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | rfl <;> simp [S]
    | one => simp [S]
    | mul a b _ _ ha hb =>
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb ⊢
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, one_mul, mul_one, hx, hy, hcomm, hxx, hyx, true_or, or_true]
    | inv a _ ha =>
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, mul_inv_rev, hxi, hyi, hcomm, true_or, or_true]
  have hfin : Finite (Subgroup.closure ({x, y} : Set G)) :=
    Set.Finite.subset (Finset.finite_toSet S) hsub
  refine ⟨Nat.card_pos.ne', ?_⟩
  calc Nat.card (Subgroup.closure ({x, y} : Set G))
      = Nat.card ((Subgroup.closure ({x, y} : Set G)) : Set G) := rfl
    _ ≤ Nat.card (S : Set G) := Nat.card_mono (Finset.finite_toSet S) hsub
    _ = S.card := Nat.card_eq_finsetCard S
    _ ≤ 4 := by
      simp only [S]
      exact Finset.card_le_four

end CertificateChecks.KernelRu

end
