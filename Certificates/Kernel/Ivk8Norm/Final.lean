module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Norm
public import CFSG.Certificates.Kernel.Ivk8NormSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.M22
public import Certificates.Kernel.Ivk8Norm.M12
public import Certificates.Kernel.Ivk8Norm.M22
public import Certificates.Kernel.Ivk8Norm.L34

public section

namespace CFSG.KS.Ivk8Norm.Final

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.Sporadic.Schreier CFSG.Certificates
  CFSG.Sporadic.Mathieu CFSG.KS.PK

variable {n : ℕ}

theorem cover_of_conjOK {r A B : VP n} {cs : List (VP n)} (hcs : ∃ c₁ c₂ c₃, cs = [c₁, c₂, c₃])
    (h : conjOK r (cs.zip [A, B, mulV A B]) = true) :
    ∀ e ∈ [pkp A, pkp B, pkp A * pkp B], ∃ c ∈ cs.map pkp, c * pkp r * c⁻¹ = e := by
  obtain ⟨c₁, c₂, c₃, rfl⟩ := hcs
  have hs := conjOK_spec h
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨pkp c₁, by simp, hs (c₁, A) (by simp)⟩
  · exact ⟨pkp c₂, by simp, hs (c₂, B) (by simp)⟩
  · refine ⟨pkp c₃, by simp, ?_⟩
    rw [← pkp_mulV A B]
    exact hs (c₃, mulV A B) (by simp)

theorem noThree_of_checks {G S₀ K : Subgroup (Equiv.Perm (Fin n))} (hS₀G : S₀ ≤ G)
    {A B r : VP n} {cs L : List (VP n)} (hAS : pkp A ∈ S₀) (hBS : pkp B ∈ S₀)
    (hkl : kleinOK A B = true) (hK : ∀ x ∈ G, x * pkp r = pkp r * x → x ∈ K)
    (h9 : ¬ 9 ∣ Nat.card K) (hKL : ∀ y, y ∈ K ↔ y ∈ L.map pkp) (hcsG : ∀ c ∈ cs, pkp c ∈ G)
    (hcs3 : ∃ c₁ c₂ c₃, cs = [c₁, c₂, c₃]) (hconj : conjOK r (cs.zip [A, B, mulV A B]) = true)
    (hchk : chk A B cs L = true) {k : ℕ} (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup (Equiv.Perm (Fin n)), P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup 3 W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin n))) → W = ⊥ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kleinOK_spec hkl
  refine CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.noThree_of_cent hS₀G hAS hBS h1 h2 h3 h4 h5 h6 hK h9
    (cs := cs.map pkp) ?_ (cover_of_conjOK hcs3 hconj) ?_ hS₀
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact hcsG c' hc'
  · intro y hy c hc ho
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact chk_spec_perm hchk y ((hKL y).1 hy) c' hc' ho

theorem mem_buildStrong {S : List (Equiv.Perm (Fin n))} (ws : List (List ℤ))
    {s : Equiv.Perm (Fin n)} (hs : s ∈ S) : s ∈ buildStrong S ws := by
  induction ws generalizing S with
  | nil => exact hs
  | cons w ws ih => exact ih (List.mem_append_left _ hs)

section M12

open CFSG.KS.Ivk8Norm.M12

theorem m12_gens : gens.map pkp = [m12gA, m12gB] := by
  rw [eq_of_vals (l₂ := [codeV m12gA, codeV m12gB]) ch5244_gens]
  simp [pkp_codeV]

theorem m12_gens_mem'' : ∀ g ∈ [m12gA, m12gB], g ∈ CFSG.Blueprint.NativeSporadic.M12 := by
  rw [← m12Certificate_originalSubgroup]
  exact m12_gens_mem

theorem m12_strong : m12CentQ1.strong.toList = strong.map pkp := by
  have e1 : m12CentQ1 = certificate (by decide) ((m12CentWords1.map (evV gens)).map pkp)
      m12CentChainWords1 #v[0, 1, 2] (by decide) := by
    rw [← map_evalCodes, m12_gens]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ (eq_of_vals ch5244_strong)

theorem m12_noThree :
    ∀ P W : Subgroup (Equiv.Perm (Fin 12)), P ≤ CFSG.Blueprint.NativeSporadic.M12 →
      W ≤ CFSG.Blueprint.NativeSporadic.M12 → Nat.card P = 2 ^ 6 → IsPGroup 3 W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 12))) → W = ⊥ := by
  have hw : A :: B :: cs = (wA :: wB :: wcs).map (evV gens) :=
    eq_of_vals (by rw [List.map_map]; exact ch5244_words)
  rw [List.map_cons, List.map_cons, List.cons.injEq, List.cons.injEq] at hw
  obtain ⟨hA, hB, hcs⟩ := hw
  have hev : ∀ w, pkp (evV gens w) ∈ CFSG.Blueprint.NativeSporadic.M12 := fun w => by
    rw [pkp_evV, m12_gens]
    exact evalCodes_mem _ m12_gens_mem'' w
  have hr : pkp (gens.getD 0 (oneV 12)) = m12gA := by
    rw [eq_of_vals (l₂ := [codeV m12gA, codeV m12gB]) ch5244_gens]
    simp [pkp_codeV]
  have hrep : m12Rep1 = m12gA := by
    simp [m12Rep1, m12InvReps, m12InvRepWords, evalCodes]
  have hQ : ValidSchreier m12CentQ1 := m12_oddcore_cent1.1
  refine noThree_of_checks (K := m12CentQ1.originalSubgroup) le_rfl (hA ▸ hev wA) (hB ▸ hev wB)
    ch5244_klein ?_ ?_ ?_ ?_ ⟨_, _, _, rfl⟩ ch5244_conj ch5244_chk ?_
  · intro x hx hxr
    rw [hr] at hxr
    rw [← CFSG.ComponentClassification.M12Cover.centralizerIn_m12Rep1, hrep]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  · rw [m12_rep_data1.2.2.2.1]
    norm_num
  · intro y
    rw [← mem_enumeration_iff m12CentQ1 hQ, enumeration_eq_enumV m12CentQ1 strong m12_strong]
    rfl
  · intro c hc
    have hc' : c ∈ cs := hc
    rw [hcs] at hc'
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc'
    exact hev w
  · rw [m12_card]
    norm_num

end M12

section M22

open CFSG.KS.Ivk8Norm.M22

theorem m22_gens : gens.map pkp = [m22gA, m22gB] := by
  rw [eq_of_vals (l₂ := [codeV m22gA, codeV m22gB]) ch5245_gens]
  simp [pkp_codeV]

theorem m22_gens_mem'' : ∀ g ∈ [m22gA, m22gB], g ∈ CFSG.Blueprint.NativeSporadic.M22 := by
  rw [← m22Certificate_originalSubgroup]
  exact m22_gens_mem

theorem m22_strong : m22CentQ1.strong.toList = strong.map pkp := by
  have e1 : m22CentQ1 = certificate (by decide) ((m22CentWords1.map (evV gens)).map pkp)
      m22CentChainWords1 #v[0, 1, 2] (by decide) := by
    rw [← map_evalCodes, m22_gens]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ (eq_of_vals ch5245_strong)

theorem m22_noThree :
    ∀ P W : Subgroup (Equiv.Perm (Fin 22)), P ≤ CFSG.Blueprint.NativeSporadic.M22 →
      W ≤ CFSG.Blueprint.NativeSporadic.M22 → Nat.card P = 2 ^ 7 → IsPGroup 3 W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 22))) → W = ⊥ := by
  have hw : A :: B :: cs = (wA :: wB :: wcs).map (evV gens) :=
    eq_of_vals (by rw [List.map_map]; exact ch5245_words)
  rw [List.map_cons, List.map_cons, List.cons.injEq, List.cons.injEq] at hw
  obtain ⟨hA, hB, hcs⟩ := hw
  have hev : ∀ w, pkp (evV gens w) ∈ CFSG.Blueprint.NativeSporadic.M22 := fun w => by
    rw [pkp_evV, m22_gens]
    exact evalCodes_mem _ m22_gens_mem'' w
  have hr : pkp (gens.getD 0 (oneV 22)) = m22gA := by
    rw [eq_of_vals (l₂ := [codeV m22gA, codeV m22gB]) ch5245_gens]
    simp [pkp_codeV]
  have hrep : m22Rep1 = m22gA := by
    simp [m22Rep1, m22InvReps, m22InvRepWords, evalCodes]
  have hQ : ValidSchreier m22CentQ1 := m22_oddcore_cent1.1
  refine noThree_of_checks (K := m22CentQ1.originalSubgroup) le_rfl (hA ▸ hev wA) (hB ▸ hev wB)
    ch5245_klein ?_ ?_ ?_ ?_ ⟨_, _, _, rfl⟩ ch5245_conj ch5245_chk ?_
  · intro x hx hxr
    rw [hr] at hxr
    rw [← CFSG.EvenSporadicStandard.HypOne.M22.centralizerIn_rep1, hrep]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  · rw [m22_rep_data1.2.2.2.1]
    norm_num
  · intro y
    rw [← mem_enumeration_iff m22CentQ1 hQ, enumeration_eq_enumV m22CentQ1 strong m22_strong]
    rfl
  · intro c hc
    have hc' : c ∈ cs := hc
    rw [hcs] at hc'
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc'
    exact hev w
  · rw [m22_card]
    norm_num

end M22

section L34

open CFSG.KS.Ivk8Norm.L34 CFSG.ComponentClassification.PSL3Four Certificates.Ivk8Weak.L34

set_option maxRecDepth 100000

theorem l34_gens : gens.map pkp = [g₁, g₂, g₃, g₄, g₅, g₆] := by
  rw [eq_of_vals (l₁ := gens) (l₂ := [g₁, g₂, g₃, g₄, g₅, g₆].map codeV)
    (by rw [List.map_map]; exact ch5247_gens)]
  simp [pkp_codeV]

theorem l34_gens_mem : ∀ g ∈ [g₁, g₂, g₃, g₄, g₅, g₆], g ∈ R := fun g hg =>
  Subgroup.subset_closure (by simpa using hg)

theorem l34_rStrong : rChain.strong.toList = rStrong.map pkp := by
  have e1 : rChain = certificate (by decide) (gens.map pkp) rWords #v[0, 1, 6, 3, 5, 2]
      (by decide) := by
    rw [l34_gens]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ (eq_of_vals ch5247_rStrong)

theorem l34_kStrong : cent.strong.toList = kStrong.map pkp := by
  have e1 : cent = certificate (by decide) ((centGens.map (evV gens)).map pkp) centWords
      #v[13, 11, 5] (by decide) := by
    rw [← map_evalCodes, l34_gens]
    rfl
  rw [e1]
  exact certificate_strong_eq _ _ _ _ _ _ (eq_of_vals ch5247_kStrong)

theorem l34_cent_valid : ValidSchreier cent := by
  have e1 : cent = certificate (by decide) ((centGens.map (evV gens)).map pkp) centWords
      #v[13, 11, 5] (by decide) := by
    rw [← map_evalCodes, l34_gens]
    rfl
  have h := l34_kStrong
  rw [e1] at h ⊢
  exact check_of_schV _ _ _ _ _ kStrong h ch5247_kSch

theorem l34_r : pkp r = r₁ := by
  have h : r = evV gens wr := Subtype.ext (beq_iff_eq.1 ch5247_r).symm
  rw [h, pkp_evV, l34_gens]
  simp [evalCodes, wr, r₁, pow_two, mul_assoc]

theorem l34_conjClass : 315 ≤ (conjClass R r₁).ncard := by
  have h := conjClass₁.2
  have hsub : Subtype.val '' (ConjClasses.mk r₁R).carrier ⊆ conjClass R r₁ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hy
    obtain ⟨c, hc⟩ := isConj_iff.1 hy.symm
    exact ⟨c, c.2, by rw [← hc]; rfl⟩
  have h1 := Set.ncard_le_ncard hsub (conjClass_finite R r₁)
  rw [Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq, h] at h1
  exact h1

theorem l34_cent_card : Nat.card cent.originalSubgroup = 768 := by
  rw [← cent.orderCertificate_eq_card l34_cent_valid, orderCertificate_eq_ordV cent kStrong
    l34_kStrong]
  exact beq_iff_eq.1 ch5247_kOrd

theorem l34_cent_le : cent.originalSubgroup ≤ centralizerIn R r₁ := by
  have hcomm := commOK_spec ch5247_kComm
  rw [l34_r] at hcomm
  have hS := l34_kStrong
  rw [cent, certificate_strong_toList] at hS
  rw [cent, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hg' : g ∈ centGens.map (evalCodes [g₁, g₂, g₃, g₄, g₅, g₆]) := hg
  refine mem_centralizerIn.2 ⟨?_, ?_⟩
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg'
    exact evalCodes_mem _ l34_gens_mem w
  · have hgs : g ∈ kStrong.map pkp := by
      rw [← hS]
      exact mem_buildStrong _ hg'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hgs
    exact hcomm s hs

theorem l34_cent_eq : centralizerIn R r₁ = cent.originalSubgroup :=
  centralizerIn_eq_of_le R r₁ l34_cent_le l34_conjClass (by rw [l34_cent_card, card_R])

theorem l34_facts :
    ValidSchreier rChain ∧ rChain.orderCertificate = 241920 ∧
    ∀ P W : Subgroup (Equiv.Perm (Fin 42)), P ≤ S → W ≤ R → Nat.card P = 2 ^ 6 → IsPGroup 3 W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 42))) → W = ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · have e1 : rChain = certificate (by decide) (gens.map pkp) rWords #v[0, 1, 6, 3, 5, 2]
        (by decide) := by
      rw [l34_gens]
      rfl
    have h := l34_rStrong
    rw [e1] at h ⊢
    exact check_of_schV _ _ _ _ _ rStrong h ch5247_rSch
  · have hb : rChain.base = #v[0, 1, 6, 3, 5, 2] := rfl
    rw [orderCertificate_eq_ordV rChain rStrong l34_rStrong, hb]
    exact beq_iff_eq.1 ch5247_rOrd
  have hw : A :: B :: cs = (wordA :: wordB :: wcs).map (evV gens) :=
    eq_of_vals (by rw [List.map_map]; exact ch5247_words)
  rw [List.map_cons, List.map_cons, List.cons.injEq, List.cons.injEq] at hw
  obtain ⟨hA, hB, hcs⟩ := hw
  have hev : ∀ w, pkp (evV gens w) = evalCodes [g₁, g₂, g₃, g₄, g₅, g₆] w := fun w => by
    rw [pkp_evV, l34_gens]
  have hS3 : ∀ w, (∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 3) → pkp (evV gens w) ∈ S := fun w hw' => by
    rw [hev]
    refine CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.evalCodes_mem_prefix (m := 3)
      (fun i hi => ?_) w hw'
    rw [S]
    interval_cases i
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hQ := l34_cent_valid
  refine noThree_of_checks (K := cent.originalSubgroup) S_le_R
    (hA ▸ hS3 wordA (by decide)) (hB ▸ hS3 wordB (by decide)) ch5247_klein ?_ ?_ ?_ ?_
    ⟨_, _, _, rfl⟩ ch5247_conj ch5247_chk ?_
  · intro x hx hxr
    rw [l34_r] at hxr
    rw [← l34_cent_eq]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  · rw [l34_cent_card]
    norm_num
  · intro y
    rw [← mem_enumeration_iff cent hQ, enumeration_eq_enumV cent kStrong l34_kStrong]
    rfl
  · intro c hc
    have hc' : c ∈ cs := hc
    rw [hcs] at hc'
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc'
    rw [hev]
    exact evalCodes_mem _ l34_gens_mem w
  · rw [card_S]
    norm_num

end L34

end CFSG.KS.Ivk8Norm.Final

end
