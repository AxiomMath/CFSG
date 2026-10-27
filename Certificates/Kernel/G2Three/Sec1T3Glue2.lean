module

public import Certificates.Kernel.G2Three.Sec1T3Glue
public import Certificates.Kernel.G2Three.Sec1T3CChecks
public import Certificates.Kernel.G2Three.Sec1T3DChecks
public import Certificates.Kernel.G2Three.Sec1T3EChecks
public import CFSG.Certificates.Kernel.G2Three.Sec1T3ESound
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F14ab
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F14c
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F14de
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F14fg
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F15a
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F15bc
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3.Glue

open Subgroup CFSG.KC.Loop CFSG.KD.G2Three.Sec1T3 CFSG.KC.G2Three.Sec1T3
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

theorem s3_hdist : ∀ k < 408, ∀ k' < 408, latM LMP k = latM LMP k' → k = k' :=
  latSort_inj s3e_sort s3_ord (by norm_num)

theorem s3_rgChunk : ∀ j < 8, rgAllK LMP OR RG 408 (51 * j) 51 = true := by
  intro j hj
  interval_cases j
  exacts [s3c_rgAll0, s3c_rgAll1, s3c_rgAll2, s3c_rgAll3, s3c_rgAll4, s3c_rgAll5, s3c_rgAll6,
    s3c_rgAll7]

theorem s3_rgAll : ∀ k < 408, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧
    rgAllK LMP OR RG 408 lo w = true := fun k hk =>
  ⟨51 * (k / 51), 51, by omega, by omega, by norm_num, s3_rgChunk _ (by omega)⟩

theorem s3_hall : ∀ k < 408, ∀ h < 408, 2 * ordAt OR h = ordAt OR k →
    subM (entL LMP h) (entL LMP k) = true → outB (entL LMP h) (rgAt RG k) = true := by
  intro k hk h hh ho hs
  have hc := rgAllK_spec (s3_rgChunk (k / 51) (by omega)) (by norm_num) (by norm_num)
    (k - 51 * (k / 51)) (by omega) h hh
  have e : 51 * (k / 51) + (k - 51 * (k / 51)) = k := by omega
  rw [e] at hc
  exact hc ho hs

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

theorem s3_gen {elt : ℕ → G} (hR : RealT elt PT PC IV SQ)
    (hg : ∀ s < 6, elt (s + 1) = sGen (frameOf m) s) :
    ∀ k < 408, ∀ K : Subgroup G, RepM elt (entL LMP k) (K : Set G) →
      K = closure (rgSet elt RG k) := by
  intro k hk K hK
  have hl := s3_lat hR hg
  have h2 : IsPGroup 2 (frameOf m).Sσ := by
    have hc := f11_card hR (f11_Ss hR hg (by
      have h := s3a_f11
      unfold f11K at h
      simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
      exact h.2.2.2.1))
    refine IsPGroup.of_card (n := 7) ?_
    rw [hc]
    have h := s3a_f11
    unfold f11K at h
    simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.2.2.2.2]
    norm_num
  exact (rg_closure hR.inj (L := LMP) (G₀ := (frameOf m).Sσ) hl h2 (by norm_num) s3c_rg
    (ordK_spec s3_ord (by norm_num)) s3_hall hk hK).2

omit [Finite G] in
theorem s3_pRank_eq [Finite G] (V : Subgroup G) : CFSG.pRank 2 ↥V = CFSG.Open.pRank 2 V := by
  have hset : {k : ℕ | ∃ A : Subgroup ↥V, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ k} =
      {k : ℕ | ∃ E : Subgroup G, E ≤ V ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    ext k
    constructor
    · rintro ⟨A, hA, hAcard⟩
      exact ⟨A.map V.subtype, Subgroup.map_subtype_le A,
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)).mpr
          (CFSG.IsElementaryAbelian.subgroup_map hA V.subtype),
        by rw [Subgroup.card_map_of_injective (Subtype.coe_injective), hAcard]⟩
    · rintro ⟨E, hEV, hE, hEcard⟩
      have e : Nat.card (E.subgroupOf V) = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEV).toEquiv
      exact ⟨E.subgroupOf V,
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)).mp (hE.subgroupOf V),
        by rw [e, hEcard]⟩
  rw [CFSG.pRank, hset, CFSG.Open.pRank]

theorem s3_cards {elt : ℕ → G} (hR : RealT elt PT PC IV SQ)
    (hg : ∀ s < 6, elt (s + 1) = sGen (frameOf m) s) :
    Nat.card (frameOf m).S = 64 ∧ Nat.card (frameOf m).Sσ = 128 := by
  have h := s3a_f11
  unfold f11K at h
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, c5, p5, c6, p6⟩ := h
  exact ⟨by rw [f11_card hR (f11_S hR (fun s hs => hg s (by omega)) c5), p5],
    by rw [f11_card hR (f11_Ss hR hg c6), p6]⟩

variable (m) in
theorem s3_fact14 : (frameOf m).Fact14 := by
  obtain ⟨elt, hR, hg⟩ := s3_real m
  have hg5 : ∀ s < 5, elt (s + 1) = sGen (frameOf m) s := fun s hs => hg s (by omega)
  have hlat := s3_lat hR hg
  have hc := s3_cards hR hg
  have h2 : IsPGroup 2 (frameOf m).Sσ := IsPGroup.of_card (n := 7) (by rw [hc.2]; norm_num)
  have h12 := fact14_12_of_twin hR hg5 (by norm_num) hlat (s3_gen hR hg) s3c_f14a s3c_f14b
  have h3 := fact14_3_of_twin hR hg5 h2 hc.1 h12.1.1 hlat (by norm_num) s3_ord s3c_rg s3_rgAll
    s3c_f14c
  have h45 := fact14_45_of_twin hR hg (by norm_num) hlat (h12.1.2.1.trans h12.1.2.2.1) s3c_f14d
    s3c_f14e
  have h67 := fact14_67_of_twin hR hg5 hlat s3_hdist (by norm_num) s3_ord s3c_rg s3_rgAll
    s3c_f14f s3c_f14g
  unfold Frame.Fact14
  rw [s3_pRank_eq]
  exact ⟨h12.1, h12.2, h3, h45.1, h45.2, h67.1, h67.2⟩

variable (m) in
theorem s3_fact15 : (frameOf m).Fact15 := by
  obtain ⟨elt, hR, hg⟩ := s3_real m
  have hlat := s3_lat hR hg
  have hc := s3_cards hR hg
  have h2 : IsPGroup 2 (frameOf m).Sσ := IsPGroup.of_card (n := 7) (by rw [hc.2]; norm_num)
  have h12 := fact15_12_of_twin hR hg (by norm_num) hlat s3d_f15a
  have h36 := fact15_3456_of_twin hR hg hlat (by norm_num) s3_ord h2 s3c_rg s3_rgAll s3d_f15b
    s3d_f15c
  exact ⟨h12.1, h12.2, h36⟩

variable (m) in
theorem s3_facts : (frameOf m).Fact11 m.L ∧ (frameOf m).Fact12 ∧ (frameOf m).Fact13 ∧
    (frameOf m).Fact14 ∧ (frameOf m).Fact15 :=
  ⟨s3_fact11, s3_fact12, s3_fact13, s3_fact14 m, s3_fact15 m⟩

end CFSG.KD.G2Three.Sec1T3.Glue

end
