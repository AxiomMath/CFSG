module

public import Certificates.Kernel.StdOdd.Cent7.Glue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenSylowPred

public section

namespace CFSG.KD.StdOdd.Cent7

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.LieType.Chevalley


theorem c0Facts_K :
    (∀ s : Rgrp, orderOf s = 7 →
      GLAPPrimeCoreOf 7 (Subgroup.centralizer ({s} : Set Rgrp)) = ⊥) ∧
    ∀ s : Rgrp, orderOf s = 7 → ∀ r ∈ Subgroup.centralizer ({s} : Set Rgrp), orderOf r ≠ 6 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite Rgrp := rgrp_finite
  have hprop : ∀ {s : Rgrp},
      ((∀ r ∈ Subgroup.centralizer ({s} : Set Rgrp), orderOf r ≠ 6) ∧
        ∀ N : Subgroup Rgrp, N ≤ Subgroup.centralizer ({s} : Set Rgrp) →
          (∀ c ∈ Subgroup.centralizer ({s} : Set Rgrp), ∀ x ∈ N, c * x * c⁻¹ ∈ N) →
          Nat.Coprime 7 (Nat.card N) → N = ⊥) →
      GLAPPrimeCoreOf 7 (Subgroup.centralizer ({s} : Set Rgrp)) = ⊥ ∧
        ∀ r ∈ Subgroup.centralizer ({s} : Set Rgrp), orderOf r ≠ 6 := fun h =>
    ⟨h.2 _ (CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le _)
      (fun g hg x hx => GLAPPrimeCoreOf_conj_mem g hg x hx)
      (coprime_card_GLAPPrimeCoreOf (by norm_num) _), h.1⟩
  have hA := hprop centFacts_rep7A_K
  have hB := hprop centFacts_rep7B_K
  have hp3 : ¬ 7 ^ 3 ∣ Nat.card Rgrp := by
    rw [C2E6Std.card_stdGroup]
    norm_num
  obtain ⟨x₀, y₀, hx₀, hy₀, hc, hind, h0, hi⟩ := sylow_seven_fusion
  have hall := forall_of_sylow_elementary hp3 hx₀ hy₀ hc hind ({rep7A, rep7B} : Set Rgrp)
    (by
      rcases h0 with h | h
      · exact ⟨rep7A, by simp, h⟩
      · exact ⟨rep7B, by simp, h⟩)
    (fun i hi' => by
      rcases hi i hi' with h | h
      · exact ⟨rep7A, by simp, h⟩
      · exact ⟨rep7B, by simp, h⟩)
    (fun y => GLAPPrimeCoreOf 7 (Subgroup.centralizer ({y} : Set Rgrp)) = ⊥ ∧
      ∀ r ∈ Subgroup.centralizer ({y} : Set Rgrp), orderOf r ≠ 6)
    (fun a b hab ha => centralizerProp_of_isConj 7 hab ha)
    (fun a b hab ha => centralizerProp_of_zpowers_eq 7 hab ha)
    (by
      intro r hr
      rcases hr with rfl | rfl
      · exact hA
      · exact hB)
  exact ⟨fun s hs => (hall s hs).1, fun s hs => (hall s hs).2⟩

end CFSG.KD.StdOdd.Cent7

end
