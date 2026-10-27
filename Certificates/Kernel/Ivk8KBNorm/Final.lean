module

public import CFSG.Certificates.Kernel.Ivk8KBNormSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Balance
public import Certificates.Kernel.Ivk8KBNorm.L34
public import Certificates.Kernel.Ivk8Norm.Final

public section

namespace CFSG.KS.Ivk8KBNorm.Final

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8KBNorm CFSG.Sporadic.Schreier
  CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.KS.PK CFSG.ComponentClassification.PSL3Four
  Certificates.Ivk8KB Pointwise

theorem exists_conj_mem_of_card {G : Type*} [Group G] [Finite G] {K P : Subgroup G} (hPK : P ≤ K)
    {p : ℕ} [Fact p.Prime] (hP : Nat.card P = p ^ (Nat.card K).factorization p) {y : G}
    (hyK : y ∈ K) (hy : y ^ p = 1) (hy1 : y ≠ 1) : ∃ k ∈ K, k * y * k⁻¹ ∈ P := by
  have hcard : Nat.card (P.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
  have hyK1 : (⟨y, hyK⟩ : K) ^ p = 1 := Subtype.ext (by simpa using hy)
  have hyKne : (⟨y, hyK⟩ : K) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hp : IsPGroup p (Subgroup.zpowers (⟨y, hyK⟩ : K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hyK1 hyKne, pow_one])
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T (Sylow.ofCard (P.subgroupOf K) hcard)
  have hmem : MulAut.conj g • (⟨y, hyK⟩ : K) ∈ ((g • T : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hT (Subgroup.mem_zpowers _))
  rw [hg, Sylow.coe_ofCard, Subgroup.mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
  exact ⟨g, g.2, by simpa using hmem⟩

set_option maxRecDepth 100000

theorem ev_eq (w : List ℤ) :
    pkp (evV Ivk8Norm.L34.gens w) = evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w := by
  rw [pkp_evV, Ivk8Norm.Final.l34_gens]

theorem ev_mem_R (w : List ℤ) : evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w ∈ R :=
  evalCodes_mem _ Ivk8Norm.Final.l34_gens_mem w

theorem ev_mem_S (w : List ℤ) (hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 3) :
    evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w ∈ S := by
  refine CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.evalCodes_mem_prefix (m := 3) (fun i hi => ?_) w hw
  rw [S]
  interval_cases i
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem eq_evV_of_vals {l : List (VP 42)} {ws : List (List ℤ)}
    (h : (l.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true) :
    l = ws.map (evV Ivk8Norm.L34.gens) :=
  eq_of_vals (by rw [List.map_map]; exact h)

theorem map_pkp_of_vals {l : List (VP 42)} {ws : List (List ℤ)}
    (h : (l.map Subtype.val == ws.map fun w => (evV Ivk8Norm.L34.gens w).1) = true) :
    l.map pkp = ws.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := by
  rw [eq_evV_of_vals h, ← map_evalCodes, Ivk8Norm.Final.l34_gens]

theorem pkp_eq_of_val {v : VP 42} {w : List ℤ}
    (h : ((evV Ivk8Norm.L34.gens w).1 == v.1) = true) :
    pkp v = evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w := by
  rw [← ev_eq, Subtype.ext (beq_iff_eq.1 h)]

theorem pkp_r4 : pkp L34.r4 = r₄ := by
  rw [pkp_eq_of_val L34.ch5250_r4]
  simp [evalCodes, wordR4, r₄]

theorem d1_sq : pkp L34.d1 * pkp L34.d1 = r₁ := by
  rw [← pkp_mulV, ← Ivk8Norm.Final.l34_r]
  exact eq_of_not_difV L34.ch5250_d1sq

@[expose] def mChain : RawSchreierDatum 42 :=
  certificate (by decide) (L34.mGens.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆])) [] #v[25, 24]
    (by decide)

@[expose] def pChain : RawSchreierDatum 42 :=
  certificate (by decide) (L34.pGens.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆])) [] #v[2, 6]
    (by decide)

theorem mChain_eq : mChain = certificate (by decide)
    ((L34.mGens.map (evV Ivk8Norm.L34.gens)).map pkp) [] #v[25, 24] (by decide) := by
  rw [← map_evalCodes, Ivk8Norm.Final.l34_gens]
  rfl

theorem pChain_eq : pChain = certificate (by decide)
    ((L34.pGens.map (evV Ivk8Norm.L34.gens)).map pkp) [] #v[2, 6] (by decide) := by
  rw [← map_evalCodes, Ivk8Norm.Final.l34_gens]
  rfl

theorem mChain_strong : mChain.strong.toList = L34.mStrong.map pkp := by
  rw [mChain_eq]
  exact certificate_strong_eq _ _ _ _ _ _
    (by rw [buildV]; exact (eq_evV_of_vals L34.ch5250_mGens).symm)

theorem pChain_strong : pChain.strong.toList = L34.pStrong.map pkp := by
  rw [pChain_eq]
  exact certificate_strong_eq _ _ _ _ _ _
    (by rw [buildV]; exact (eq_evV_of_vals L34.ch5250_pGens).symm)

theorem mChain_valid : ValidSchreier mChain := by
  have h := mChain_strong
  rw [mChain_eq] at h ⊢
  exact check_of_schV _ _ _ _ _ L34.mStrong h L34.ch5250_mSch

theorem pChain_valid : ValidSchreier pChain := by
  have h := pChain_strong
  rw [pChain_eq] at h ⊢
  exact check_of_schV _ _ _ _ _ L34.pStrong h L34.ch5250_pSch

theorem mChain_card : Nat.card mChain.originalSubgroup = 64 := by
  rw [← mChain.orderCertificate_eq_card mChain_valid,
    orderCertificate_eq_ordV mChain L34.mStrong mChain_strong]
  exact beq_iff_eq.1 L34.ch5250_mOrd

theorem pChain_card : Nat.card pChain.originalSubgroup = 27 := by
  rw [← pChain.orderCertificate_eq_card pChain_valid,
    orderCertificate_eq_ordV pChain L34.pStrong pChain_strong]
  exact beq_iff_eq.1 L34.ch5250_pOrd

theorem cent_fact :
    ∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d := by
  have hsq := d1_sq
  have hd1S : pkp L34.d1 ∈ S := by
    rw [pkp_eq_of_val L34.ch5250_d1]
    exact ev_mem_S wordD1 (by decide)
  have hd1C : pkp L34.d1 ∈ C₁ :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (by rw [← hsq, mul_assoc]), hd1S⟩
  have hcomm : ∀ x, x * pkp L34.d1 = pkp L34.d1 * x → x * r₁ = r₁ * x := by
    intro x hx
    rw [← hsq, ← mul_assoc, hx, mul_assoc, hx, mul_assoc]
  have hM : centralizerIn Ivk8Norm.L34.cent.originalSubgroup (pkp L34.d1) =
      mChain.originalSubgroup := by
    refine centralizerIn_eq_of_le _ _ (c := 12) ?_ ?_ ?_
    · rw [mChain, certificate_originalSubgroup, Subgroup.closure_le]
      intro g hg
      have hg' : g ∈ L34.mGens.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := hg
      have hgs : g ∈ L34.mStrong.map pkp := by
        rw [map_pkp_of_vals L34.ch5250_mGens]
        exact hg'
      obtain ⟨w, -, hw⟩ := List.mem_map.1 hg'
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hgs
      have hc := commOK_spec L34.ch5250_mComm s hs
      refine mem_centralizerIn.2 ⟨?_, hc⟩
      rw [← Ivk8Norm.Final.l34_cent_eq]
      refine mem_centralizerIn.2 ⟨?_, hcomm _ hc⟩
      rw [← hw]
      exact ev_mem_R w
    · have hD : L34.D.map pkp = L34.cs.map fun c => pkp c * pkp L34.d1 * (pkp c)⁻¹ := by
        rw [← conjsV_map, eq_of_vals L34.ch5250_conjs]
      have hnd := distinctV_nodup L34.ch5250_distinct
      have hcs := map_pkp_of_vals L34.ch5250_cs
      have hsub : ((L34.D.map pkp).toFinset : Set (Equiv.Perm (Fin 42))) ⊆
          conjClass Ivk8Norm.L34.cent.originalSubgroup (pkp L34.d1) := by
        intro x hx
        rw [Finset.mem_coe, List.mem_toFinset, hD] at hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
        refine ⟨pkp c, ?_, rfl⟩
        rw [← Ivk8Norm.Final.l34_cent_eq]
        refine mem_centralizerIn.2 ⟨?_, ?_⟩
        · have hc' : pkp c ∈ L34.wcs.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := by
            rw [← hcs]
            exact List.mem_map_of_mem hc
          obtain ⟨w, -, hw⟩ := List.mem_map.1 hc'
          rw [← hw]
          exact ev_mem_R w
        · rw [← Ivk8Norm.Final.l34_r]
          exact commOK_spec L34.ch5250_csComm c hc
      have h1 := Set.ncard_le_ncard hsub (conjClass_finite _ _)
      rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map] at h1
      exact h1
    · rw [mChain_card, Ivk8Norm.Final.l34_cent_card]
  intro x hxR hx1 hx3
  refine ⟨pkp L34.d1, hd1C, fun hc => ?_⟩
  have hxH : x ∈ Ivk8Norm.L34.cent.originalSubgroup := by
    rw [← Ivk8Norm.Final.l34_cent_eq]
    exact mem_centralizerIn.2 ⟨hxR, hcomm x hc.symm⟩
  have hxM : x ∈ mChain.originalSubgroup := by
    rw [← hM]
    exact mem_centralizerIn.2 ⟨hxH, hc.symm⟩
  have hdvd : orderOf x ∣ 64 := by
    rw [← mChain_card]
    exact Subgroup.orderOf_dvd_natCard _ hxM
  rw [orderOf_eq_prime hx3 hx1] at hdvd
  norm_num at hdvd

theorem factorization_864 : (864 : ℕ).factorization 3 = 3 := by
  have h : (864 : ℕ) = 3 ^ 3 * 32 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 3),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 32)]

theorem fix_fact :
    ∀ y ∈ R, y ∉ S → y ^ 3 = 1 → r₄ * y = y * r₄ → ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1 := by
  have h864 : Nat.card ↥(Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 864 := by
    have h := CFSG.ComponentClassification.GrSLit.card_centralizer_mul_of_isConj
      (IsConj.refl r₄R) conjClass₄.2
    change Nat.card ↥(Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R) * 280 =
      241920 at h
    omega
  have hP : pChain.originalSubgroup ≤
      Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    rw [pChain, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    have hg' : g ∈ L34.pGens.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := hg
    have hgs : g ∈ L34.pStrong.map pkp := by
      rw [map_pkp_of_vals L34.ch5250_pGens]
      exact hg'
    obtain ⟨w, -, hw⟩ := List.mem_map.1 hg'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hgs
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · rw [← pkp_r4]
      exact commOK_spec L34.ch5250_pComm s hs
    · rw [← hw]
      exact ev_mem_R w
  have hd4S : pkp L34.d4 ∈ S := by
    rw [pkp_eq_of_val L34.ch5250_d4]
    exact ev_mem_S wordD4 (by decide)
  have hd4c : pkp L34.d4 * r₄ = r₄ * pkp L34.d4 := by
    rw [← pkp_r4]
    exact commOK_spec L34.ch5250_d4Comm L34.d4 (List.mem_singleton_self _)
  have hwE : ∀ w ∈ wordsE, ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 3 := by decide
  intro y hyR hyS hy3 hyc
  have hy1 : y ≠ 1 := fun h => hyS (h ▸ S.one_mem)
  have hyK : y ∈ Subgroup.centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ R :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hyc.symm, hyR⟩
  obtain ⟨k, hk, hz⟩ := exists_conj_mem_of_card hP (p := 3)
    (by rw [pChain_card, h864, factorization_864]; norm_num) hyK hy3 hy1
  obtain ⟨hkc, hkR⟩ := Subgroup.mem_inf.1 hk
  have hkc' : Commute k r₄ := Subgroup.mem_centralizer_singleton_iff.1 hkc
  have hz3 : (k * y * k⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hz1 : k * y * k⁻¹ ≠ 1 := fun h => hy1 (conj_eq_one_iff.1 h)
  have hzE : k * y * k⁻¹ ∉ L34.E.map pkp := by
    rw [map_pkp_of_vals L34.ch5250_E]
    intro h
    obtain ⟨w, hw, hwz⟩ := List.mem_map.1 h
    exact hyS (conj_mem_S' hkR (hwz ▸ ev_mem_S w (hwE w hw)))
  have hzP : k * y * k⁻¹ ∈ (enumV L34.pStrong pChain.base).map pkp := by
    rw [← enumeration_eq_enumV pChain L34.pStrong pChain_strong, mem_enumeration_iff pChain
      pChain_valid]
    exact hz
  have hne := fixOK_spec L34.ch5250_fix _ hzP hz3 hz1 hzE
  refine ⟨k⁻¹ * pkp L34.d4 * k⁻¹⁻¹, Subgroup.mem_inf.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, conj_mem_S (R.inv_mem hkR) hd4S⟩, ?_⟩
  · exact (hkc'.inv_left.mul_left hd4c).mul_left hkc'.inv_left.inv_left
  have e : y * ((k⁻¹ * pkp L34.d4 * k⁻¹⁻¹) * y * (k⁻¹ * pkp L34.d4 * k⁻¹⁻¹)⁻¹) =
      k⁻¹ * ((k * y * k⁻¹) * (pkp L34.d4 * (k * y * k⁻¹) * (pkp L34.d4)⁻¹)) * k⁻¹⁻¹ := by
    group
  rw [e, conj_pow]
  exact fun h => hne (conj_eq_one_iff.1 h)

theorem cent_fix :
    (∀ x ∈ R, x ≠ 1 → x ^ 3 = 1 → ∃ d ∈ C₁, d * x ≠ x * d) ∧
    (∀ y ∈ R, y ∉ S → y ^ 3 = 1 → r₄ * y = y * r₄ → ∃ d ∈ C₄, (y * (d * y * d⁻¹)) ^ 3 ≠ 1) :=
  ⟨cent_fact, fix_fact⟩

end CFSG.KS.Ivk8KBNorm.Final

end
