module

public import Certificates.Kernel.WrTwin.E29Facts

public section

namespace CFSG.KD.WrTwin

open CFSG.ClassicalInvolution.Q3.E29Data CFSG.ClassicalInvolution.Q3.AE

theorem mkQ8_eq_iff' {x y : Wr 8} : mkQ 8 x = mkQ 8 y ↔ x = y ∨ x = y * Wr.allOnes 8 := by
  have hπ : (Wr.allOnes 8)⁻¹ = Wr.allOnes 8 := inv_eq_of_mul_eq_one_right (allOnes_mul_self 8)
  rw [mkQ_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (inv_mul_eq_one.mp h)
    · right
      calc x = y * (x⁻¹ * y)⁻¹ := by group
        _ = y * Wr.allOnes 8 := by rw [h, hπ]
  · rintro (h | h)
    · left
      rw [h]
      group
    · right
      rw [h, mul_inv_rev, hπ, mul_assoc, inv_mul_cancel, mul_one]

theorem eqPi_iff' {x y : Wr 8} : eqPi x y = true ↔ mkQ 8 x = mkQ 8 y := by
  rw [mkQ8_eq_iff']
  simp only [eqPi, Bool.or_eq_true, decide_eq_true_eq]

theorem e29_rows : ∀ d ∈ e29ConjData, mkQ 8 (nG d.1 * nG (2 * d.2.1 + d.2.2.1) * (nG d.1)⁻¹) =
    mkQ 8 (nWord d.2.2.2.1 d.2.2.2.2) := fun d hd => mkQ8_eq_iff'.mpr (e29_rows_hold d hd)

theorem e29_conjOK : conjOK29 = true := by decide +kernel

theorem e29_conj : ∀ j < 28, cycPerm8 (e29Conj.getD j []) ∈ agl32 ∧
    Equiv.Perm.sign (cycPerm8 (e29Conj.getD j [])) = 1 := by
  intro j hj
  have h := of_decide_eq_true (List.all_eq_true.mp e29_conjOK j (List.mem_range.mpr hj))
  exact h

theorem e29_nodupM0 : nodupM0 = true := by decide +kernel

theorem e29_nodup : ∀ s < 8, ∀ t < 8, s ≠ t → mkQ 8 ((n8 0).getD s 1) ≠ mkQ 8 ((n8 0).getD t 1) := by
  intro s hs t ht hst heq
  have h1 := List.all_eq_true.mp e29_nodupM0 s (List.mem_range.mpr hs)
  have h2 := List.all_eq_true.mp h1 t (List.mem_range.mpr ht)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact hst h2
  · rw [eqPi_iff'.mpr heq] at h2
    exact Bool.noConfusion h2

theorem e29_distinctOK : distinctOK29 = true := by decide +kernel

theorem e29_distinct : ∀ j < 28, ∀ k < 28, j ≠ k → ∀ W ∈ localWords29,
    mkQ 8 (nG (2 * j)) ≠ mkQ 8 (nWord k W) := by
  intro j hj k hk hne W hW heq
  have h1 := List.all_eq_true.mp e29_distinctOK j (List.mem_range.mpr hj)
  have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exact hne h2
  · have h3 : (n8 k).any (eqPi (nG (2 * j))) = true := by
      rw [List.any_eq_true]
      exact ⟨nWord k W, List.mem_map_of_mem hW, eqPi_iff'.mpr heq⟩
    rw [h3] at h2
    exact Bool.noConfusion h2

theorem e29_partnerOK : partnerOK29 = true := by decide +kernel

theorem e29_partner : ∀ p ∈ e29Partners,
    p < 28 ∧ p ≠ 0 ∧ mkQ 8 (nG (2 * p) * nG (2 * p)) = mkQ 8 (nA * nA) := by
  intro p hp
  have h1 := List.all_eq_true.mp e29_partnerOK p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
  obtain ⟨⟨h2, h3⟩, h4⟩ := h1
  exact ⟨h2, h3, eqPi_iff'.mp h4⟩

theorem e29_y3OK : y3OK29 = true := by decide +kernel

theorem e29_y3 : nY3 * nY3 * nY3 = 1 ∧
    (cycPerm8 e29Y3 ∈ agl32 ∧ Equiv.Perm.sign (cycPerm8 e29Y3) = 1) ∧
    (∀ r ∈ e29Y3Rows, mkQ 8 (nY3 * nG (2 * r.1 + r.2.1) * nY3⁻¹) = mkQ 8 (nWord r.1 r.2.2)) ∧
    ∀ k ∈ 0 :: e29Partners, mkQ 8 (nY3 * nG (2 * k)) ≠ mkQ 8 (nG (2 * k) * nY3) := by
  have h := e29_y3OK
  simp only [y3OK29, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun r hr => eqPi_iff'.mp (h3 r hr), fun k hk heq => ?_⟩
  have h6 := h4 k hk
  rw [eqPi_iff'.mpr heq] at h6
  exact Bool.noConfusion h6

theorem e29_even : (evenFin0 ()).card = 64 := by decide +kernel

end CFSG.KD.WrTwin

end
