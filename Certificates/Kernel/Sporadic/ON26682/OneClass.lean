module

public import CFSG.Sporadic.Schreier.ONCentralQuotient
public import CFSG.Sporadic.Schreier.ONStandardAction
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSFuse
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobLemma39N
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.Sporadic.Schreier.ONSylowCenter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CertificateChecks.KernelSpor.ON26682

open Subgroup CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
  CFSG.EvenSporadicStandard.Solomon78 CFSG.ComponentClassification

theorem conj_core26682 {H : Type*} [Group H] {z x g v h : H} (hz : z ∈ center H)
    (hgx : g * x * g⁻¹ = x * z) (hxx : x * x = 1)
    (hcz : ∀ w ∈ center H, w * w = 1 → w = 1 ∨ w = z) (hvv : v * v = 1)
    (hw : (h * x * h⁻¹)⁻¹ * v ∈ center H) : ∃ c : H, c * x * c⁻¹ = v := by
  have hv : v = h * x * h⁻¹ * ((h * x * h⁻¹)⁻¹ * v) := (mul_inv_cancel_left _ _).symm
  generalize (h * x * h⁻¹)⁻¹ * v = w at hv hw
  subst hv
  have hwc : h * x * h⁻¹ * w = w * (h * x * h⁻¹) := mem_center_iff.1 hw _
  have hY : h * x * h⁻¹ * (h * x * h⁻¹) = 1 := by
    calc h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
      _ = 1 := by rw [hxx]; group
  have hww : w * w = 1 := by
    have e1 : h * x * h⁻¹ * w * (h * x * h⁻¹ * w) =
        h * x * h⁻¹ * (w * (h * x * h⁻¹)) * w := by group
    rw [← hwc, hvv] at e1
    calc w * w = h * x * h⁻¹ * (h * x * h⁻¹) * (w * w) := by rw [hY, one_mul]
      _ = h * x * h⁻¹ * (h * x * h⁻¹ * w) * w := by group
      _ = 1 := e1.symm
  rcases hcz w hw hww with rfl | rfl
  · exact ⟨h, (mul_one _).symm⟩
  · refine ⟨h * g, ?_⟩
    calc h * g * x * (h * g)⁻¹ = h * (g * x * g⁻¹) * h⁻¹ := by group
      _ = h * x * (w * h⁻¹) := by rw [hgx]; group
      _ = h * x * h⁻¹ * w := by rw [← mem_center_iff.1 hz h⁻¹]; group

section ON


theorem center_sq26682 (hqq : onq * onq = onz) {y : Equiv.Perm (Fin N)}
    (hy : y ∈ (center ↥onL).map onL.subtype) (hyy : y * y = 1) : y = 1 ∨ y = onz := by
  have hc : y ∈ CFSG.centerIn onL := by
    rw [CFSG.centerIn_eq_map_center]
    exact hy
  rw [onL_centerIn, onQ] at hc
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  have hk : (4 : ℤ) ∣ 2 * k := by
    have : onq ^ (2 * k) = 1 := by rw [two_mul, zpow_add, hyy]
    have := orderOf_dvd_iff_zpow_eq_one.2 this
    rwa [orderOf_onq] at this
  obtain ⟨m, rfl⟩ : (2 : ℤ) ∣ k := by omega
  have hq2 : onq ^ (2 : ℤ) = onz := by rw [zpow_two]; exact hqq
  have hz2 : onz ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact onz_sq
  rw [zpow_mul, hq2]
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
  · left
    rw [hj, zpow_mul, hz2, one_zpow]
  · right
    rw [hj, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

theorem onz_mem26682 (hqq : onq * onq = onz) : onz ∈ onL := by
  rw [← hqq]
  exact onL.mul_mem onq_mem_L onq_mem_L

theorem onz_center26682 (hqq : onq * onq = onz) : onz ∈ (center ↥onL).map onL.subtype := by
  have h1 : onz ∈ CFSG.centerIn onL := by
    rw [onL_centerIn, onQ]
    exact ⟨2, by simp only [zpow_two]; exact hqq⟩
  rwa [CFSG.centerIn_eq_map_center] at h1

theorem modConj26682 {v w : ↥onL} (hv : v * v = 1) (hv1 : v ∉ center ↥onL) (hw : w * w = 1)
    (hw1 : w ∉ center ↥onL) : ∃ h : ↥onL, (h * w * h⁻¹)⁻¹ * v ∈ center ↥onL := by
  obtain ⟨e⟩ := PSL3Four.nonempty_equiv_of_stated (↥onX) onX_classicalModel
  let E : ↥onL ⧸ center ↥onL ≃* ↥PSL3Four.S := lQuotEquiv.trans e
  let φ : ↥onL →* ↥PSL3Four.S := E.toMonoidHom.comp (QuotientGroup.mk' (center ↥onL))
  have hφ : ∀ u, φ u = E (u : ↥onL ⧸ center ↥onL) := fun _ => rfl
  have key : ∀ u : ↥onL, u * u = 1 → u ∉ center ↥onL →
      ∃ s ∈ PSL3Four.S, s * PSL3Four.g₂ * s⁻¹ = (φ u : Equiv.Perm (Fin 42)) := by
    intro u hu hu1
    refine CatFactsSmall.L34.one_class (φ u).2 ?_ ?_
    · rw [← Subgroup.coe_mul, ← map_mul, hu, map_one, Subgroup.coe_one]
    · intro h1
      apply hu1
      have h2 : φ u = 1 := Subtype.ext h1
      rw [hφ, MulEquiv.map_eq_one_iff] at h2
      exact (QuotientGroup.eq_one_iff u).1 h2
  obtain ⟨s1, hs1, e1⟩ := key v hv hv1
  obtain ⟨s2, hs2, e2⟩ := key w hw hw1
  have hsurj : Function.Surjective φ :=
    E.surjective.comp (QuotientGroup.mk'_surjective (center ↥onL))
  obtain ⟨h, hh⟩ := hsurj ⟨s1 * s2⁻¹, PSL3Four.S.mul_mem hs1 (PSL3Four.S.inv_mem hs2)⟩
  refine ⟨h, ?_⟩
  have h3 : φ (h * w * h⁻¹) = φ v := by
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, hh, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← e1,
      ← e2]
    group
  rw [hφ, hφ] at h3
  exact QuotientGroup.eq.1 (E.injective h3)

theorem oneClass26682 (hqq : onq * onq = onz) {x g : Equiv.Perm (Fin N)} (hx : x ∈ onL)
    (hxx : x * x = 1) (hxc : x ∉ (center ↥onL).map onL.subtype) (hg : g ∈ onL)
    (hgx : g * x * g⁻¹ = x * onz) : OneClassOutside onL := by
  suffices H : ∀ v ∈ onL, v * v = 1 → v ∉ (center ↥onL).map onL.subtype →
      ∃ c ∈ onL, c * x * c⁻¹ = v by
    intro v hv v' hv' hvv hv'v' _ _ hvc hv'c
    obtain ⟨c1, hc1, rfl⟩ := H v hv hvv hvc
    obtain ⟨c2, hc2, rfl⟩ := H v' hv' hv'v' hv'c
    exact ⟨c2 * c1⁻¹, onL.mul_mem hc2 (onL.inv_mem hc1), by group⟩
  intro v hv hvv hvc
  have hzL := onz_mem26682 hqq
  have hZc : (⟨onz, hzL⟩ : ↥onL) ∈ center ↥onL := by
    obtain ⟨u, hu, hu'⟩ := onz_center26682 hqq
    have : u = ⟨onz, hzL⟩ := Subtype.ext hu'
    rwa [← this]
  have hcz : ∀ w ∈ center ↥onL, w * w = 1 → w = 1 ∨ w = ⟨onz, hzL⟩ := by
    intro w hw hww
    rcases center_sq26682 hqq ⟨w, hw, rfl⟩ (congrArg Subtype.val hww) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨h, hh⟩ := modConj26682 (v := ⟨v, hv⟩) (w := ⟨x, hx⟩) (Subtype.ext hvv)
    (fun h => hvc ⟨_, h, rfl⟩) (Subtype.ext hxx) (fun h => hxc ⟨_, h, rfl⟩)
  obtain ⟨c, hc⟩ := conj_core26682 (g := ⟨g, hg⟩) hZc (Subtype.ext hgx) (Subtype.ext hxx) hcz
    (Subtype.ext hvv) hh
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end ON

end CertificateChecks.KernelSpor.ON26682

end
