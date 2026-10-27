
module

public import Certificates.Kernel.J4Count.StarsBase

public import Certificates.Kernel.J4Count.HOrder

@[expose] public section

namespace CertificateChecks.KernelJ4Count.Stars

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.Mathieu
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs CertificateChecks.KernelJ4Q

instance (priority := high) hjQuotNormal : ((Eg uJ 11).subgroupOf Hj).Normal :=
  (Subgroup.normal_subgroupOf_iff Eg_le_Hj).2 fun h g hh hg => Hj_normalizes_Eg matFacts g hg h hh

theorem centralizer_Hj :
    ∀ x ∈ Hj, (∀ y ∈ Eg uJ 11, x * y = y * x) → x ∈ Eg uJ 11 := by
  refine centralizer_le_of_chain (elem_uJ matFacts) Hj Eg_le_Hj (card_Eg_uJ matFacts) bJ
    (fun i => eta_mem_Eg 11 le_rfl _) cntJ tJ 5 (fun j hj k hk => tJ_mem_Kc matFacts hj hk)
    (fun j hj k hk k' hk' h => tJ_distinct matFacts hj hk hk' h) ?_
  rw [CertificateChecks.KernelJ4Count.card_Hj']
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  unfold cntJ
  rw [chain_card]
  norm_num

theorem ker_starHom : starHom.ker = (Eg uJ 11).subgroupOf Hj := by
  have hM := matFacts
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hfix : ∀ i : Fin 24, starMap g i = i := fun i => by
      have := congrArg (fun p : Equiv.Perm (Fin 24) => p i) hg
      simpa [starHom] using this
    have hOK : ∀ i < 24, StarOK (g : J) i i := fun i hi => by
      have := starMap_spec g ⟨i, hi⟩
      rwa [hfix ⟨i, hi⟩] at this
    obtain ⟨-, -, -, -, hint, hcov, hbasis⟩ := star_facts
    have hduad : ∀ d ∈ duadMasks, (g : J) * eta uJ 11 d * (g : J)⁻¹ = eta uJ 11 d := by
      intro d hd
      obtain ⟨i, hi, j, hj, hij, hdi, hdj⟩ := hcov d hd
      obtain ⟨c₁, hc₁, e₁⟩ := hOK i hi d hdi
      obtain ⟨c₂, hc₂, e₂⟩ := hOK j hj d hdj
      have hc12 : c₁ = c₂ :=
        eta_inj hM c₁ (mem_star_lt hi hc₁) c₂ (mem_star_lt hj hc₂) (e₁.symm.trans e₂)
      have hc1d : c₁ = d := hint i hi j hj hij c₁ hc₁ (hc12 ▸ hc₂) d hdi hdj
      rw [e₁, hc1d]
    have hle : Eg uJ 11 ≤ Subgroup.centralizer ({(g : J)} : Set J) := by
      rw [Eg, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := hduad (2 ^ j) (hbasis j hj)
      rw [eta_two_pow hj] at h1
      calc (g : J) * uJ j = ((g : J) * uJ j * (g : J)⁻¹) * (g : J) := by group
        _ = uJ j * (g : J) := by rw [h1]
    have hcomm : ∀ y ∈ Eg uJ 11, (g : J) * y = y * (g : J) := fun y hy =>
      Subgroup.mem_centralizer_iff.1 (hle hy) (g : J) rfl
    exact centralizer_Hj g g.2 hcomm
  · intro hg
    ext i
    have hOK : StarOK (g : J) i i := fun c hc => by
      refine ⟨c, hc, ?_⟩
      have hc' : eta uJ 11 c ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl c
      have := Eg_comm (elem_uJ hM) hg hc'
      calc (g : J) * eta uJ 11 c * (g : J)⁻¹ = eta uJ 11 c * (g : J) * (g : J)⁻¹ := by rw [this]
        _ = eta uJ 11 c := by group
    exact congrArg Fin.val (starMap_eq (g := g) (i := i) hOK)

theorem card_Hj_quotient : Nat.card (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) = 244823040 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Eg uJ 11).subgroupOf Hj)
  have h2 : Nat.card ((Eg uJ 11).subgroupOf Hj) = 2 ^ 11 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).toEquiv]
    exact card_Eg_uJ matFacts
  rw [CertificateChecks.KernelJ4Count.card_Hj', h2] at h1
  omega

theorem range_starHom_eq : starHom.range = CFSG.Blueprint.NativeSporadic.M24 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [range_starHom, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact tauOf_mem (by norm_num)
  · rw [card_M24]
    have : Nat.card starHom.range = 244823040 := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange starHom).toEquiv, ker_starHom,
        card_Hj_quotient]
    omega

theorem isSimpleGroup_Hj_quotient : IsSimpleGroup (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) := by
  have e1 : (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) ≃* ↥starHom.range :=
    (QuotientGroup.quotientMulEquivOfEq ker_starHom.symm).trans
      (QuotientGroup.quotientKerEquivRange starHom)
  have e2 : ↥starHom.range ≃* ↥CFSG.Blueprint.NativeSporadic.M24 :=
    MulEquiv.subgroupCongr range_starHom_eq
  have := fam_m24_simplicity.2.2
  exact (e1.trans e2).isSimpleGroup

end CertificateChecks.KernelJ4Count.Stars

end
