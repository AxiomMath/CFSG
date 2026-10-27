module

public import Certificates.Kernel.OmegaCY.B0
public import Certificates.Kernel.OmegaCY.B2
public import CFSG.Certificates.Kernel.OmegaCY.Bridge

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OmegaCY Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] noncomputable def cySig (c cb : ℕ → P45) (x : ℕ) (k : ℕ) : P45 :=
  if k = 1 then c (ixF x 0) else if k = 2 then c (ixF x 1) else if k = 3 then cb (ixF x 6)
  else if k = 4 then c (ixF x 2) else if k = 5 then cb (ixF x 7) else if k = 6 then c (ixF x 3)
  else 1

theorem ixF_lt (x m : ℕ) : ixF x m < 16 := Nat.lt_succ_of_le Nat.and_le_right

theorem card_prod_top {B : Subgroup P45} {n : ℕ} (hB : Nat.card B = n) :
    Nat.card (B.prod (⊤ : Subgroup ℤˣ)) = n * 2 := by
  rw [Nat.card_congr (prodEquiv B ⊤).toEquiv, Nat.card_prod, hB, Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_units_int]

theorem lemmaY_case
    {BT : ℕ → ℕ} {x : ℕ} {B2 : Subgroup P45} {cb : ℕ → P45}
    (hcb : ∀ i < 16, PRep 45 6 (BT i) (cb i) ∧ cb i ∈ B2) (hB2 : Nat.card B2 = 16)
    (hcase : caseK 45 6 B0Z.T BT cyZ x cyTab = true)
    {H : Type*} [Group H] (Φ : H →* P45 × ℤˣ) (hΦ : Function.Injective Φ) (α : H →* H)
    (hα : ∀ y, α (α y) = y) {t z : H} (hΦt : Φ t = (1, -1))
    (hΦz : Φ z = (Certificates.OmegaT0.z0 (), 1)) (hαt : α t = t * z) (hαz : α z = z)
    (hrange : ∀ g, g ∈ CFSG.OddStandard.SmallF3.Omega.B0.prod ⊤ ∨ g ∈ B2.prod ⊤ → ∃ y, Φ y = g)
    (h02 : ∀ y, Φ y ∈ CFSG.OddStandard.SmallF3.Omega.B0.prod ⊤ → Φ (α y) ∈ B2.prod ⊤)
    (h20 : ∀ y, Φ y ∈ B2.prod ⊤ → Φ (α y) ∈ CFSG.OddStandard.SmallF3.Omega.B0.prod ⊤) :
    ∃ y : H, y⁻¹ * α y * (y⁻¹ * α y) = 1 ∧ y⁻¹ * α y ≠ 1 ∧ y⁻¹ * α y ≠ z := by
  obtain ⟨c, hc, -⟩ := b0_enum
  obtain ⟨he1, he4, he5, hgk⟩ := caseK_parts hcase
  set σ := cySig c cb x with hσ
  have hG : ∀ i < 6, PRep 45 6 (genOf 45 6 B0Z.T BT x (i + 1)) (σ (i + 1)) := by
    intro i hi
    interval_cases i
    · exact (hc _ (ixF_lt x 0)).1
    · exact (hc _ (ixF_lt x 1)).1
    · exact (hcb _ (ixF_lt x 6)).1
    · exact (hc _ (ixF_lt x 2)).1
    · exact (hcb _ (ixF_lt x 7)).1
    · exact (hc _ (ixF_lt x 3)).1
  have ht : tabOK cyTab = true := by
    have h := hgk
    unfold gensK at h
    simp only [cy_bAndD, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨hr, hne⟩ := gensK_sound (by norm_num) (by norm_num) hG hgk
  have hσ1 : σ 1 = Certificates.OmegaT0.z0 () :=
    (eqP_sound he1 (prep_cOf _) (hG 0 (by norm_num))).symm
  have hσ1B : σ 1 = cb (ixF x 4) := (eqP_sound he4 (hcb _ (ixF_lt x 4)).1 (hG 0 (by norm_num))).symm
  have hσ2B : σ 2 = cb (ixF x 5) := (eqP_sound he5 (hcb _ (ixF_lt x 5)).1 (hG 1 (by norm_num))).symm
  have hcard0 : Nat.card (CFSG.OddStandard.SmallF3.Omega.B0.prod (⊤ : Subgroup ℤˣ)) ≤ 32 := by
    rw [card_prod_top CFSG.OddStandard.SmallF3.Omega.card_B0]
    norm_num
  have hcard2 : Nat.card (B2.prod (⊤ : Subgroup ℤˣ)) ≤ 32 := by
    rw [card_prod_top hB2]
  have hg0 : ∀ i < 7, i ≠ 3 → i ≠ 5 →
      cyGen σ i ∈ CFSG.OddStandard.SmallF3.Omega.B0.prod ⊤ := by
    intro i hi h3 h5
    rw [mem_prod]
    refine ⟨?_, mem_top _⟩
    interval_cases i
    · exact one_mem _
    · exact (hc _ (ixF_lt x 0)).2
    · exact (hc _ (ixF_lt x 1)).2
    · exact absurd rfl h3
    · exact (hc _ (ixF_lt x 2)).2
    · exact absurd rfl h5
    · exact (hc _ (ixF_lt x 3)).2
  have hg2 : ∀ i < 7, i ≠ 4 → i ≠ 6 → cyGen σ i ∈ B2.prod ⊤ := by
    intro i hi h4 h6
    rw [mem_prod]
    refine ⟨?_, mem_top _⟩
    interval_cases i
    · exact one_mem _
    · change σ 1 ∈ B2
      rw [hσ1B]
      exact (hcb _ (ixF_lt x 4)).2
    · change σ 2 ∈ B2
      rw [hσ2B]
      exact (hcb _ (ixF_lt x 5)).2
    · exact (hcb _ (ixF_lt x 6)).2
    · exact absurd rfl h4
    · exact (hcb _ (ixF_lt x 7)).2
    · exact absurd rfl h6
  exact lemmaY_of_srch cySearch ht hr hne _ _ hcard0 hcard2 hg0 hg2 Φ hΦ α hα
    (by rw [hΦt]; rfl) (by rw [hΦz, ← hσ1]; rfl) hαt hαz hrange h02 h20

theorem lemmaY_of_model
    {T B0 B2 : Subgroup P45} {y2 : P45} (hT0 : T0 ≤ T)
    (hTA : T ≤ A) (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T) (hw0 : w ∉ T0)
    (hM : Certificates.OmegaS107.M107 T B2 y2) (hB0 : B0 ≤ T0)
    (hB0c : ∀ a ∈ B0, ∀ b ∈ B0, a * b = b * a) (hB0n : Nat.card B0 = 16)
    {H : Type*} [Group H] (Φ : H →* P45 × ℤˣ) (hΦ : Function.Injective Φ) (α : H →* H)
    (hα : ∀ y, α (α y) = y) {t z : H} (hΦt : Φ t = (1, -1))
    (hΦz : Φ z = (Certificates.OmegaT0.z0 (), 1)) (hαt : α t = t * z) (hαz : α z = z)
    (hrange : ∀ g, g ∈ B0.prod ⊤ ∨ g ∈ B2.prod ⊤ → ∃ y, Φ y = g)
    (h02 : ∀ y, Φ y ∈ B0.prod ⊤ → Φ (α y) ∈ B2.prod ⊤)
    (h20 : ∀ y, Φ y ∈ B2.prod ⊤ → Φ (α y) ∈ B0.prod ⊤) :
    ∃ y : H, y⁻¹ * α y * (y⁻¹ * α y) = 1 ∧ y⁻¹ * α y ≠ 1 ∧ y⁻¹ * α y ≠ z := by
  have hB := CFSG.OddStandard.SmallF3.Omega.eq_B0_of_abelian hB0 hB0c (by rw [hB0n]; norm_num)
  subst hB
  obtain ⟨j, hj, rfl⟩ := b2_eq_bz hT0 hTA hT2 hw hw0 hM
  interval_cases j
  · obtain ⟨cb, hcb, hcard⟩ := bz_enum0
    exact lemmaY_case hcb hcard cyCase0 Φ hΦ α hα hΦt hΦz hαt hαz hrange h02 h20
  · obtain ⟨cb, hcb, hcard⟩ := bz_enum1
    exact lemmaY_case hcb hcard cyCase1 Φ hΦ α hα hΦt hΦz hαt hαz hrange h02 h20
  · obtain ⟨cb, hcb, hcard⟩ := bz_enum2
    exact lemmaY_case hcb hcard cyCase2 Φ hΦ α hα hΦt hΦz hαt hαz hrange h02 h20

end CertificateChecks.KernelA45

end
