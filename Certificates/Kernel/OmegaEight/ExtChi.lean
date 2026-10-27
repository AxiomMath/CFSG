module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchExt

public section

namespace CertificateChecks.KernelO8.ExtChi

open CFSG.EvenSmallLie.OmegaEight.SpBranch

theorem chiOK_ext {N : ℕ} {mul : ℕ → ℕ → ℕ} {F : ℕ → ℕ} {z : ℕ} {gens : List ℕ} {b : List Bool}
    (χ χ' : Array Bool) (hsize : χ'.size = 2 * N) (hχ' : ∀ c < 2 * N, χ'[c]! = χ[c % N]!)
    (hmulN : ∀ a c, a < N → c < N → mul a c < N)
    (hhom : ∀ a c, a < N → c < N → χ[mul a c]! = (χ[a]! ^^ χ[c]!)) (h0 : χ[0]! = false)
    (hgens : ∀ j < gens.length, gens.getD j 0 < N ∧ χ[gens.getD j 0]! = b.getD j false)
    (hF : ∀ d < N, F d < N ∧ χ[F d]! = χ[d]!) (hz : z < N ∧ χ[z]! = false)
    (hb : b.getD gens.length false = false) :
    chiOK (extMul N mul F z) (gens ++ [N]) (2 * N) b χ' = true := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le z) hz.1
  have lo : ∀ r < N, χ'[r]! = χ[r]! := fun r hr => by
    rw [hχ' r (by omega), Nat.mod_eq_of_lt hr]
  have hi : ∀ r < N, χ'[r + N]! = χ[r]! := fun r hr => by
    rw [hχ' (r + N) (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hr]
  unfold chiOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  refine ⟨⟨hsize, by rw [lo 0 hN, h0]⟩, fun c hc j hj => ?_⟩
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · have hgd : (gens ++ [N]).getD j 0 = gens.getD j 0 := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [hgd]
    obtain ⟨hgl, hgχ⟩ := hgens j hj
    by_cases hcN : c < N
    · rw [extMul, ite_eq_left hcN, ite_eq_left hgl, lo _ (hmulN _ _ hcN hgl), hhom _ _ hcN hgl, lo c hcN,
        hgχ]
    · have hc' : c - N < N := by omega
      have hce : c = (c - N) + N := by omega
      obtain ⟨hFl, hFχ⟩ := hF _ hgl
      rw [extMul, ite_eq_right hcN, ite_eq_left hgl, hi _ (hmulN _ _ hc' hFl), hhom _ _ hc' hFl, hFχ, hgχ,
        hce, hi _ hc', Nat.add_sub_cancel]
  · have hgd : (gens ++ [N]).getD gens.length 0 = N := by
      simp [List.getD_eq_getElem?_getD]
    rw [hgd, hb, Bool.xor_false]
    by_cases hcN : c < N
    · rw [extMul, ite_eq_left hcN, ite_eq_right (lt_irrefl N), Nat.sub_self, hi _ (hmulN _ _ hcN hN),
        hhom _ _ hcN hN, h0, Bool.xor_false, lo c hcN]
    · have hc' : c - N < N := by omega
      have hce : c = (c - N) + N := by omega
      obtain ⟨hFl, hFχ⟩ := hF 0 hN
      have h1 := hmulN _ _ hc' hFl
      rw [extMul, ite_eq_right hcN, ite_eq_right (lt_irrefl N), Nat.sub_self, lo _ (hmulN _ _ h1 hz.1),
        hhom _ _ h1 hz.1, hhom _ _ hc' hFl, hFχ, h0, hz.2, Bool.xor_false, Bool.xor_false, hce,
        hi _ hc', Nat.add_sub_cancel]

end CertificateChecks.KernelO8.ExtChi

end
