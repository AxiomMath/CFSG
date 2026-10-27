module

public import Certificates.Kernel.Eight89K.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverHom

public section

namespace CFSG.KC.Eight89K

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 KInputs Subgroup

theorem card_model3_le : Nat.card model3 ≤ 1080 := by
  obtain ⟨hfin, hle⟩ := cover3_facts 1 0 (by norm_num) (by norm_num)
  obtain ⟨hs, ha, hb, habb, hc⟩ := model3_facts
  have hc3 : orderOf c3 = 3 := by
    change orderOf (s3 ^ 5) = 3
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs]; norm_num), hs]
  obtain ⟨ψ, -, -, -, hψr⟩ := exists_coverHom 3 0 0 1 0 a3 b3 c3
    (hc3 ▸ pow_orderOf_eq_one c3) (mem_center_iff.mp hc a3) (mem_center_iff.mp hc b3)
    (by rw [mul_zero, pow_zero]; exact ha) (by rw [mul_zero, pow_zero]; exact hb)
    (pow_one c3).symm (by rw [pow_zero]; exact habb)
  have hψ : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, hψr, eq_top_iff, ← closure_gens3]
    refine closure_mono fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  exact (Nat.card_le_card_of_surjective ψ hψ).trans (by simpa using hle)

theorem card_model6_le : Nat.card model6 ≤ 2160 := by
  obtain ⟨hfin, hle⟩ := cover6_facts 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hs, ha, hb, habb, hc⟩ := model6_facts
  have hc6 : orderOf c6 = 6 := by
    change orderOf (s6 ^ 5) = 6
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs]; norm_num), hs]
  obtain ⟨ψ, -, -, -, hψr⟩ := exists_coverHom 6 1 1 1 0 a6 b6 c6
    (hc6 ▸ pow_orderOf_eq_one c6) (mem_center_iff.mp hc a6) (mem_center_iff.mp hc b6)
    (by rw [mul_one]; exact ha) (by rw [mul_one]; exact hb)
    (pow_one c6).symm (by rw [pow_zero]; exact habb)
  have hψ : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, hψr, eq_top_iff, ← closure_gens6]
    refine closure_mono fun g hg => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  exact (Nat.card_le_card_of_surjective ψ hψ).trans (by simpa using hle)

end CFSG.KC.Eight89K

end
