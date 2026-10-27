module

public import Certificates.Kernel.Sporadic.Fi24G2g.Pt
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts
public import CFSG.Fischer.T46Unitary
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Sporadic.FischerOddCore.AlmostSimple

public section

namespace CertificateChecks.KernelFi24G2g

open CertificateChecks.KernelFi24 CertificateChecks.KernelFi24Fix CertificateChecks.KernelFi24Orb
  CertificateChecks.KernelFi24Ext CertificateChecks.KernelFi24G2e TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS CFSG.KC.Fi24FixC

open CFSG.Sporadic.Fi24 (R cls)
open CFSG.Sporadic.FischerOddCore (TripleFacts)
open CFSG.KD.Fi24G2d (F2D W2D)
open CFSG.KD.Fi24Orb (NM NI)
open CFSG.KD.Fi24G2e (CQL CYF)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem _root_.CFSG.Sporadic.FischerOddCore.TripleFacts.conj {r r' c : R} (h : TripleFacts r') (hc : c * r * c⁻¹ = r') :
    TripleFacts r := by
  obtain ⟨k₁, k₂, k₃, hne, hr, hfix, hcomm, hchar⟩ := h
  have hr' : r = c⁻¹ * r' * c := by rw [← hc]; group
  have hcls : ∀ k : Fin 306936, cls (c⁻¹ • k) = c⁻¹ * cls k * c := fun k => by
    rw [CFSG.Sporadic.Fi24.cls_smul_R, inv_inv]
  have hsm : ∀ l : Fin 306936, r • l = l ↔ r' • (c • l) = c • l := fun l => by
    rw [hr', mul_smul, mul_smul, inv_smul_eq_iff]
  have hcm : ∀ k l : Fin 306936, cls (c⁻¹ • k) * cls l = cls l * cls (c⁻¹ • k) ↔
      cls k * cls (c • l) = cls (c • l) * cls k := fun k l => by
    rw [hcls, CFSG.Sporadic.Fi24.cls_smul_R]
    constructor
    · intro e
      calc cls k * (c * cls l * c⁻¹) = c * ((c⁻¹ * cls k * c) * cls l) * c⁻¹ := by group
        _ = c * (cls l * (c⁻¹ * cls k * c)) * c⁻¹ := by rw [e]
        _ = c * cls l * c⁻¹ * cls k := by group
    · intro e
      calc c⁻¹ * cls k * c * cls l = c⁻¹ * (cls k * (c * cls l * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * cls l * c⁻¹ * cls k) * c := by rw [e]
        _ = cls l * (c⁻¹ * cls k * c) := by group
  have hmem : ∀ k : Fin 306936, k ∈ ({c⁻¹ • k₁, c⁻¹ • k₂, c⁻¹ • k₃} : Set (Fin 306936)) ↔
      c • k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := fun k => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_inv_smul_iff]
  refine ⟨c⁻¹ • k₁, c⁻¹ • k₂, c⁻¹ • k₃, ⟨fun e => hne.1 (smul_left_cancel _ e),
    fun e => hne.2.1 (smul_left_cancel _ e), fun e => hne.2.2 (smul_left_cancel _ e)⟩, ?_, ?_, ?_, ?_⟩
  · rw [hcls, hcls, hcls, hr', hr]
    group
  · intro k hk
    rw [hsm]
    exact hfix _ ((hmem k).1 hk)
  · intro k hk l hl
    obtain ⟨k', hk', rfl⟩ : ∃ k' ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), k = c⁻¹ • k' :=
      ⟨c • k, (hmem k).1 hk, by rw [inv_smul_smul]⟩
    rw [hcm]
    exact hcomm k' hk' _ ((hsm l).1 hl)
  · intro k hk hall
    rw [hmem]
    refine hchar _ ((hsm k).1 hk) fun l hl => ?_
    have h1 := hall (c⁻¹ • l) (by rw [hsm, smul_inv_smul]; exact hl)
    have h2 := (hcm (c • k) (c⁻¹ • l)).1 (by rw [inv_smul_smul]; exact h1)
    rwa [smul_inv_smul] at h2

theorem NM_pk {r : ℕ} (hr : r < 306936) : NM (pk hr) = r := NM_NI hr

section Bind

variable (hP : PtRank)
include hP

theorem fixed_W2D_iff (k : Fin 306936) :
    ρ (wp W2D) • k = k ↔ ∃ j < 696, F2D j = NM k := by
  have hw : ∀ g ∈ W2D, g < 12 := by decide
  have e : (ρ (wp W2D))⁻¹ • k = pk (walk_lt hw (NM_lt k.isLt)) := by
    conv_lhs => rw [← pk_NM k]
    exact smul_pk hP hw _
  have hi : ρ (wp W2D) • k = k ↔ (ρ (wp W2D))⁻¹ • k = k := by
    rw [inv_smul_eq_iff, eq_comm]
  rw [← CFSG.KD.Fi24G2d.fix_W2D_iff _ (NM_lt k.isLt), hi, e]
  constructor
  · intro h
    exact (pk_inj _ _ (h.trans (pk_NM k).symm))
  · intro h
    rw [pk_congr _ (NM_lt k.isLt) h, pk_NM]

theorem letter_fixes_F2D {g : ℕ} (hg : g ∈ W2D) {j : ℕ} (hj : j < 696) :
    CFSG.KD.Fi24Fix.TG g (F2D j) = F2D j := by
  have hg12 : g < 12 := by
    simp only [W2D, List.mem_cons, List.not_mem_nil, or_false] at hg
    omega
  have hF := (CFSG.KD.Fi24G2d.F2D_spec j hj).1
  have hlt : CFSG.KD.Fi24Fix.TG g (F2D j) < 306936 := by
    have := walk_lt (w := [g]) (by simpa using hg12) hF
    rwa [walk_cons, walk_nil] at this
  apply ψ_inj hlt hF
  rw [ψ_TG hg12 hF]
  exact clause_F2D.1 j hj g hg


theorem tripleFacts_W2D : TripleFacts (ρ (wp W2D)) := by
  obtain ⟨c0, c2, c4, -⟩ := cls_own hP
  have h0 : (37886 : ℕ) < 306936 := by norm_num
  have h2 : (22978 : ℕ) < 306936 := by norm_num
  have h4 : (22975 : ℕ) < 306936 := by norm_num
  have hprod : ρ (wp W2D) = cls (pk h0) * cls (pk h2) * cls (pk h4) := by
    rw [c0, c2, c4, ← map_mul, ← map_mul]
    congr 1
  have hown : ∀ r ∈ ([37886, 22978, 22975] : List ℕ), walk CFSG.KD.Fi24Fix.TG W2D r = r := by
    decide +kernel
  have hfixr : ∀ {r : ℕ} (hr : r < 306936), walk CFSG.KD.Fi24Fix.TG W2D r = r →
      ρ (wp W2D) • pk hr = pk hr := by
    intro r hr h
    rw [fixed_W2D_iff hP, NM_pk]
    exact (CFSG.KD.Fi24G2d.fix_W2D_iff r hr).1 h
  have hmem3 : ∀ k : Fin 306936, k ∈ ({pk h0, pk h2, pk h4} : Set (Fin 306936)) →
      ∃ g ∈ W2D, cls k = ρ (g0 g) := by
    intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl
    · exact ⟨0, by decide, c0⟩
    · exact ⟨2, by decide, c2⟩
    · exact ⟨4, by decide, c4⟩
  refine ⟨pk h0, pk h2, pk h4, ⟨fun e => absurd (pk_inj _ _ e) (by norm_num),
    fun e => absurd (pk_inj _ _ e) (by norm_num), fun e => absurd (pk_inj _ _ e) (by norm_num)⟩,
    hprod, ?_, ?_, ?_⟩
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl
    · exact hfixr h0 (hown _ (by simp))
    · exact hfixr h2 (hown _ (by simp))
    · exact hfixr h4 (hown _ (by simp))
  · intro k hk l hl
    obtain ⟨g, hg, hk'⟩ := hmem3 k hk
    obtain ⟨j, hj, hjl⟩ := (fixed_W2D_iff hP l).1 hl
    have hg12 : g < 12 := by
      simp only [W2D, List.mem_cons, List.not_mem_nil, or_false] at hg
      omega
    rw [cls_comm_iff, hk']
    conv_lhs => rw [← pk_NM l]
    rw [smul_pk_letter hP hg12]
    conv_rhs => rw [← pk_NM l]
    apply pk_congr
    rw [walk_cons, walk_nil, ← hjl, letter_fixes_F2D hP hg hj]
  · intro k hk hall
    obtain ⟨j, hj, hjk⟩ := (fixed_W2D_iff hP k).1 hk
    have hkp : k = pk (NM_lt k.isLt) := (pk_NM k).symm
    rcases clause_F2D.2 j hj with h | h | h | ⟨hw, hy, hne⟩
    · rw [hkp, pk_congr _ h0 (hjk.symm.trans h)]
      simp
    · rw [hkp, pk_congr _ h2 (hjk.symm.trans h)]
      simp
    · rw [hkp, pk_congr _ h4 (hjk.symm.trans h)]
      simp
    · exfalso
      have hFy := (CFSG.KD.Fi24G2d.F2D_spec _ hy).1
      have hl : ρ (wp W2D) • pk hFy = pk hFy := by
        rw [fixed_W2D_iff hP, NM_pk]
        exact ⟨_, hy, rfl⟩
      have hc := (cls_comm_iff k (pk hFy)).1 (hall _ hl)
      have hck : cls k = ρ ((wp (CQL j))⁻¹ * g0 0 * wp (CQL j)) := by
        rw [hkp]
        exact cls_pk_walk' hP (cq_lt j hj) _ (hw.trans hjk)
      apply hne
      have e := congrArg (fun x : Fin 306936 => f x.val) hc
      rw [f_smul hP, f_pk, hck, coe_ρ, map_mul, map_mul, map_inv, τ_g0_zero] at e
      rwa [map_inv]

end Bind

end CertificateChecks.KernelFi24G2g

end
