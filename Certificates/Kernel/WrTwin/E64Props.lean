module

public import Certificates.Kernel.WrTwin.E64Facts

public section

namespace CFSG.KD.WrTwin

open CFSG.ClassicalInvolution.Q3.E64Data CFSG.ClassicalInvolution.Q3.AE

theorem e64_conj : ∀ j < 14, cycPerm (e64Conj.getD j []) ∈ l32 ∧
    Equiv.Perm.sign (cycPerm (e64Conj.getD j [])) = 1 := by
  have h : ∀ j < 14, ((∀ s ∈ fanoLines, s.map (cycPerm (e64Conj.getD j [])).toEmbedding ∈ fanoLines ∧
      s.map (cycPerm (e64Conj.getD j []))⁻¹.toEmbedding ∈ fanoLines) ∧
      Equiv.Perm.sign (cycPerm (e64Conj.getD j [])) = 1) := by
    decide +kernel
  exact h

theorem e64_nodup : (m8 0).Nodup := by decide +kernel

theorem e64_distinct : ∀ j < 14, ∀ k < 14, j ≠ k → mG (2 * j) ∉ m8 k := by decide +kernel

theorem e64_partner :
    e64JStar < 14 ∧ e64JStar ≠ 0 ∧ mG (2 * e64JStar) * mG (2 * e64JStar) = mA * mA := by
  decide +kernel

theorem e64_y3 : mY3 * mY3 * mY3 = 1 ∧
    (cycPerm [[0, 1, 3], [4, 5, 6]] ∈ l32 ∧ Equiv.Perm.sign (cycPerm [[0, 1, 3], [4, 5, 6]]) = 1) ∧
    (∀ r ∈ e64Y3Rows, mY3 * mG (2 * r.1 + r.2.1) * mY3⁻¹ = mWord r.1 r.2.2) ∧
    mY3 * mA ≠ mA * mY3 ∧ mY3 * mG (2 * e64JStar) ≠ mG (2 * e64JStar) * mY3 := by
  have h : mY3 * mY3 * mY3 = 1 ∧
      ((∀ s ∈ fanoLines, s.map (cycPerm [[0, 1, 3], [4, 5, 6]]).toEmbedding ∈ fanoLines ∧
        s.map (cycPerm [[0, 1, 3], [4, 5, 6]])⁻¹.toEmbedding ∈ fanoLines) ∧
        Equiv.Perm.sign (cycPerm [[0, 1, 3], [4, 5, 6]]) = 1) ∧
      (∀ r ∈ e64Y3Rows, mY3 * mG (2 * r.1 + r.2.1) * mY3⁻¹ = mWord r.1 r.2.2) ∧
      mY3 * mA ≠ mA * mY3 ∧ mY3 * mG (2 * e64JStar) ≠ mG (2 * e64JStar) * mY3 := by
    decide +kernel
  exact h

theorem e64_even : (evenFin ()).card = 64 := by decide +kernel

@[expose] def fanoFrames : Finset (Fin 7 × Fin 7 × Fin 7) :=
  Finset.univ.filter fun t => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
    ({t.1, t.2.1, t.2.2} : Finset (Fin 7)) ∉ fanoLines

theorem card_fanoFrames : fanoFrames.card = 168 := by decide +kernel

theorem map_three (σ : Equiv.Perm (Fin 7)) (a b c : Fin 7) :
    ({a, b, c} : Finset (Fin 7)).map σ.toEmbedding = {σ a, σ b, σ c} := by
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.coe_toEmbedding]

theorem eq_one_of_fix {ρ : Equiv.Perm (Fin 7)} (h : ρ ∈ l32) (h0 : ρ 0 = 0) (h1 : ρ 1 = 1)
    (h2 : ρ 2 = 2) : ρ = 1 := by
  have h' : ∀ s ∈ fanoLines, s.map ρ.toEmbedding ∈ fanoLines ∧ s.map ρ⁻¹.toEmbedding ∈ fanoLines :=
    h
  have k : ∀ a b c : Fin 7, ({a, b, c} : Finset (Fin 7)) ∈ fanoLines →
      ({ρ a, ρ b, ρ c} : Finset (Fin 7)) ∈ fanoLines := fun a b c hl => by
    have := (h' _ hl).1
    rwa [map_three] at this
  have h3 : ρ 3 = 3 := by
    have := k 0 1 3 (by decide)
    rw [h0, h1] at this
    exact (by decide : ∀ y : Fin 7, ({0, 1, y} : Finset (Fin 7)) ∈ fanoLines → y = 3) _ this
  have h4 : ρ 4 = 4 := by
    have := k 1 2 4 (by decide)
    rw [h1, h2] at this
    exact (by decide : ∀ y : Fin 7, ({1, 2, y} : Finset (Fin 7)) ∈ fanoLines → y = 4) _ this
  have h6 : ρ 6 = 6 := by
    have := k 6 0 2 (by decide)
    rw [h0, h2] at this
    exact (by decide : ∀ y : Fin 7, ({y, 0, 2} : Finset (Fin 7)) ∈ fanoLines → y = 6) _ this
  have h5 : ρ 5 = 5 := by
    have := k 4 5 0 (by decide)
    rw [h4, h0] at this
    exact (by decide : ∀ y : Fin 7, ({4, y, 0} : Finset (Fin 7)) ∈ fanoLines → y = 5) _ this
  have hall : ∀ x : Fin 7, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by decide
  refine Equiv.ext fun x => ?_
  rcases hall x with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem card_l32Fin_le : (l32Fin ()).card ≤ 168 := by
  rw [← card_fanoFrames]
  refine Finset.card_le_card_of_injOn (fun σ => (σ 0, σ 1, σ 2)) ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_coe, l32Fin, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [Finset.mem_coe, fanoFrames, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨σ.injective.ne (by decide), σ.injective.ne (by decide), σ.injective.ne (by decide),
      fun hl => ?_⟩
    have := (hσ.1 _ hl).2
    rw [map_three] at this
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
    exact (by decide : ({0, 1, 2} : Finset (Fin 7)) ∉ fanoLines) this
  · intro σ hσ τ hτ he
    simp only [Finset.mem_coe, l32Fin, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hτ
    simp only [Prod.mk.injEq] at he
    have hσl : σ ∈ l32 := hσ.1
    have hτl : τ ∈ l32 := hτ.1
    have hρ := eq_one_of_fix (l32.mul_mem (l32.inv_mem hτl) hσl)
      (by rw [Equiv.Perm.mul_apply, he.1, Equiv.Perm.inv_def, Equiv.symm_apply_apply])
      (by rw [Equiv.Perm.mul_apply, he.2.1, Equiv.Perm.inv_def, Equiv.symm_apply_apply])
      (by rw [Equiv.Perm.mul_apply, he.2.2, Equiv.Perm.inv_def, Equiv.symm_apply_apply])
    exact (inv_mul_eq_one.mp hρ).symm

theorem card_l32Fin : (l32Fin ()).card = 168 :=
  le_antisymm card_l32Fin_le le_card_l32Fin

end CFSG.KD.WrTwin

end
