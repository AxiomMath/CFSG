module

public import Certificates.Kernel.Ivk8Norm.Final
public import CFSG.Certificates.Kernel.Ivk8NormPAb
public import Certificates.Certificate5244
public import Certificates.Certificate5245
public import Certificates.Certificate5247

public section

namespace CFSG.KS.Ivk8Norm.Final

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.Sporadic.Schreier CFSG.Certificates
  CFSG.Sporadic.Mathieu CFSG.KS.PK

variable {n : ℕ}

theorem not_dvd_two_pow_mul_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (a : ℕ) :
    ¬ p ∣ 2 ^ a * 3 := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

theorem noP_of_checks_free {G S₀ K : Subgroup (Equiv.Perm (Fin n))} (hS₀G : S₀ ≤ G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {A B r : VP n} {cs : List (VP n)} (hAS : pkp A ∈ S₀)
    (hBS : pkp B ∈ S₀) (hkl : kleinOK A B = true) (hK : ∀ x ∈ G, x * pkp r = pkp r * x → x ∈ K)
    (hpK : ¬ p ∣ Nat.card K) (hcsG : ∀ c ∈ cs, pkp c ∈ G) (hcs3 : ∃ c₁ c₂ c₃, cs = [c₁, c₂, c₃])
    (hconj : conjOK r (cs.zip [A, B, mulV A B]) = true) {k : ℕ}
    (hS₀ : ¬ 2 ^ (k + 1) ∣ Nat.card S₀) :
    ∀ P W : Subgroup (Equiv.Perm (Fin n)), P ≤ S₀ → W ≤ G → Nat.card P = 2 ^ k → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin n))) → W = ⊥ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kleinOK_spec hkl
  refine CFSG.KS.Ivk8NormP.noP_of_cent_free hS₀G hp hp2 hAS hBS h1 h2 h3 h4 h5 h6 hK hpK
    (cs := cs.map pkp) ?_ (cover_of_conjOK hcs3 hconj) hS₀
  intro c hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  exact hcsG c' hc'

section M12

open CFSG.KS.Ivk8Norm.M12

theorem m12_noP
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 12)), P ≤ CFSG.Blueprint.NativeSporadic.M12 →
      W ≤ CFSG.Blueprint.NativeSporadic.M12 → Nat.card P = 2 ^ 6 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 12))) → W = ⊥ := by
  by_cases hp3 : p = 3
  · subst hp3
    exact Certificates.certificate5244
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
  refine noP_of_checks_free (K := m12CentQ1.originalSubgroup) le_rfl hp hp2 (hA ▸ hev wA)
    (hB ▸ hev wB) ch5244_klein ?_ ?_ ?_ ⟨_, _, _, rfl⟩ ch5244_conj ?_
  · intro x hx hxr
    rw [hr] at hxr
    rw [← CFSG.ComponentClassification.M12Cover.centralizerIn_m12Rep1, hrep]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  · rw [m12_rep_data1.2.2.2.1]
    exact not_dvd_two_pow_mul_three hp hp2 hp3 6
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

theorem m22_noP
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 22)), P ≤ CFSG.Blueprint.NativeSporadic.M22 →
      W ≤ CFSG.Blueprint.NativeSporadic.M22 → Nat.card P = 2 ^ 7 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 22))) → W = ⊥ := by
  by_cases hp3 : p = 3
  · subst hp3
    exact Certificates.certificate5245
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
  refine noP_of_checks_free (K := m22CentQ1.originalSubgroup) le_rfl hp hp2 (hA ▸ hev wA)
    (hB ▸ hev wB) ch5245_klein ?_ ?_ ?_ ⟨_, _, _, rfl⟩ ch5245_conj ?_
  · intro x hx hxr
    rw [hr] at hxr
    rw [← CFSG.EvenSporadicStandard.HypOne.M22.centralizerIn_rep1, hrep]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  · rw [m22_rep_data1.2.2.2.1]
    exact not_dvd_two_pow_mul_three hp hp2 hp3 7
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

theorem l34_noP {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ P W : Subgroup (Equiv.Perm (Fin 42)), P ≤ S → W ≤ R → Nat.card P = 2 ^ 6 → IsPGroup p W →
      P ≤ Subgroup.normalizer (W : Set (Equiv.Perm (Fin 42))) → W = ⊥ := by
  by_cases hp3 : p = 3
  · subst hp3
    exact fun P W h1 h2 h3 h4 h5 => Certificates.certificate5247.2.2 P W h1 h2 h3 h4 h5
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
  refine noP_of_checks_free (K := cent.originalSubgroup) S_le_R hp hp2
    (hA ▸ hS3 wordA (by decide)) (hB ▸ hS3 wordB (by decide)) ch5247_klein ?_ ?_ ?_
    ⟨_, _, _, rfl⟩ ch5247_conj ?_
  · intro x hx hxr
    rw [l34_r] at hxr
    rw [← l34_cent_eq]
    exact mem_centralizerIn.2 ⟨hx, hxr⟩
  · rw [l34_cent_card]
    exact not_dvd_two_pow_mul_three hp hp2 hp3 8
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
