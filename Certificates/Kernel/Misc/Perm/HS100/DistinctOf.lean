module

public import Certificates.Data.Kernel.BfsPin
public import CFSG.Certificates.Kernel.Spor.Loops
public import Mathlib.Data.Finset.Card

public section

namespace CertificateChecks.KernelMisc.HS100.DistinctOf

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin
open CFSG.KLie.CT (orN pw2 maskN)

theorem pw2_eq (s : Nat) : pw2 s = 2 ^ s := by
  change 1 <<< s = 2 ^ s
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_orN (S : Nat → Nat) (b : Nat) :
    ∀ n, (orN n (fun k => pw2 (S k))).testBit b = true ↔ ∃ k < n, S k = b
  | 0 => by
    change Nat.testBit 0 b = true ↔ _
    simp
  | n + 1 => by
    change (pw2 (S n) ||| orN n (fun k => pw2 (S k))).testBit b = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_orN S b n, pw2_eq, Nat.testBit_two_pow,
      decide_eq_true_iff]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨k, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inr ⟨k, hk, h⟩
      · exact Or.inl h

theorem distinctK_of {N : Nat} {T S : Nat → Nat}
    (h1 : allN (Nat.sub N (nat_lit 1)) (fun k => Nat.blt (T (S k)) (T (S (Nat.succ k)))) = true)
    (h2 : allN N (fun k => Nat.blt (S k) N) = true) : distinctK N T S = true := by
  have hlt : ∀ k, k + 1 < N → T (S k) < T (S (k + 1)) := fun k hk => by
    have h := allN_spec h1 k (show k < N - 1 by omega)
    simpa only [Nat.blt_eq] using h
  have hS : ∀ k < N, S k < N := fun k hk => by
    have h := allN_spec h2 k hk
    simpa only [Nat.blt_eq] using h
  have mono : ∀ b, b < N → ∀ a < b, T (S a) < T (S b) := by
    intro b
    induction b with
    | zero => intro _ a ha; omega
    | succ b ih =>
      intro hb a ha
      have hstep := hlt b hb
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | rfl
      · exact lt_trans (ih (by omega) a h) hstep
      · exact hstep
  have inj : ∀ a < N, ∀ b < N, S a = S b → a = b := by
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with h | h | h
    · have := mono b hb a h
      rw [e] at this
      omega
    · exact h
    · have := mono a ha b h
      rw [e] at this
      omega
  have himg : (Finset.range N).image S = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨k, hk, rfl⟩ := hx
      exact hS k hk
    · rw [Finset.card_image_of_injOn fun a ha b hb e =>
        inj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e]
  have surj : ∀ x < N, ∃ k < N, S k = x := by
    intro x hx
    have hx' : x ∈ (Finset.range N).image S := by
      rw [himg]
      exact Finset.mem_range.2 hx
    simp only [Finset.mem_image, Finset.mem_range] at hx'
    exact hx'
  have h3 : orN N (fun k => pw2 (S k)) = maskN N := by
    apply Nat.eq_of_testBit_eq
    intro b
    have hm : (maskN N).testBit b = decide (b < N) := by
      change (pw2 N - 1).testBit b = _
      rw [pw2_eq, Nat.testBit_two_pow_sub_one]
    rw [hm]
    by_cases hb : b < N
    · rw [(testBit_orN S b N).2 (surj b hb)]
      simp [hb]
    · have hf : (orN N (fun k => pw2 (S k))).testBit b = false := by
        cases h : (orN N (fun k => pw2 (S k))).testBit b
        · rfl
        · obtain ⟨k, hk, rfl⟩ := (testBit_orN S b N).1 h
          exact absurd (hS k hk) hb
      rw [hf]
      simp [hb]
  unfold distinctK
  rw [h1, h2, h3]
  exact Nat.beq_refl _

end CertificateChecks.KernelMisc.HS100.DistinctOf

end
