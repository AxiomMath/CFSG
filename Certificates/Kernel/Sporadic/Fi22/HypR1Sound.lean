module

public import Certificates.Kernel.Sporadic.Fi22.HypR1
public import CFSG.Certificates.Kernel.Spor.CommBaseSound
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace CertificateChecks.KernelSpor.Fi22R1

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.ComponentClassification.M12Cover

variable {g₁ g₂ t : Equiv.Perm (Fin 3510)}

@[expose] def letterPerm (g₁ g₂ t : Equiv.Perm (Fin 3510)) (z : ℕ) : Equiv.Perm (Fin 3510) :=
  [g₂ * g₂, g₁ * (g₂ * g₂) * g₁⁻¹, t, (g₂ * g₂)⁻¹, (g₁ * (g₂ * g₂) * g₁⁻¹)⁻¹].getD z 1

private theorem prep_c {P Q : ℕ} {g h : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g)
    (hQ : PRep 3510 12 Q h) : PRep 3510 12 (Fi22X.c P Q) (g * h) :=
  prep_pcomp (by norm_num) hP hQ

private theorem pow5_eq_one {P : ℕ} {g : Equiv.Perm (Fin 3510)} (hP : PRep 3510 12 P g)
    (h : pow5 P = pidn 3510 12) : g ^ 5 = 1 := by
  have h5 : PRep 3510 12 (pow5 P) (g * (g * (g * (g * g)))) :=
    prep_c hP (prep_c hP (prep_c hP (prep_c hP hP)))
  rw [h] at h5
  have e := prep_unique h5 (prep_pidn (by norm_num) (by norm_num))
  rw [← e]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem prep_letters (h1 : PRep 3510 12 G1 g₁) (h2 : PRep 3510 12 G2 g₂) (ht : PRep 3510 12 T t) :
    (∀ z < 5, PRep 3510 12 (L z) (letterPerm g₁ g₂ t z)) ∧ (g₂ * g₂) ^ 5 = 1 ∧
      (g₁ * (g₂ * g₂) * g₁⁻¹) ^ 5 = 1 := by
  have hg := gensAll
  have hl := lettersAll
  simp only [gensOK, bAnd_eq, Bool.and_eq_true] at hg
  simp only [Fi22R1.lettersOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hl
  obtain ⟨-, -, -, -, -, hpa, -⟩ := hg
  obtain ⟨-, e0, e1, e2, hp3, hp4, h50, h51⟩ := hl
  have hai : PRep 3510 12 (Fi22X.inv G1) g₁⁻¹ := prep_inv_of_permOK h1 hpa
  have hA : PRep 3510 12 (L 0) (g₂ * g₂) := by
    rw [e0]
    exact prep_c h2 h2
  have hB : PRep 3510 12 (L 1) (g₁ * (g₂ * g₂) * g₁⁻¹) := by
    rw [e1, mul_assoc]
    exact prep_c h1 (prep_c hA hai)
  refine ⟨fun z hz => ?_, pow5_eq_one hA h50, pow5_eq_one hB h51⟩
  interval_cases z
  · exact hA
  · exact hB
  · rw [e2]
    exact ht
  · exact prep_inv_of_permOK hA hp3
  · exact prep_inv_of_permOK hB hp4

theorem comm_gens (h1 : PRep 3510 12 G1 g₁) (h2 : PRep 3510 12 G2 g₂) (ht : PRep 3510 12 T t) :
    g₁ * t = t * g₁ ∧ g₂ * t = t * g₂ := by
  have hg := gensAll
  simp only [gensOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hg
  obtain ⟨-, -, -, -, -, -, -, -, -, ha, hb⟩ := hg
  refine ⟨prep_unique (prep_c h1 ht) ?_, prep_unique (prep_c h2 ht) ?_⟩
  · rw [ha]
    exact prep_c ht h1
  · rw [hb]
    exact prep_c ht h2

theorem fourClassesLarge_R1 (K : Subgroup (Equiv.Perm (Fin 3510))) (h1 : PRep 3510 12 G1 g₁)
    (h2 : PRep 3510 12 G2 g₂) (ht : PRep 3510 12 T t) (hg1 : g₁ ∈ K) (hg2 : g₂ ∈ K)
    (htK : ∀ k ∈ K, Commute k t) : FourClassesLarge K := by
  obtain ⟨hL, ha5, hb5⟩ := prep_letters h1 h2 ht
  have hA : g₂ * g₂ ∈ K := K.mul_mem hg2 hg2
  have hB : g₁ * (g₂ * g₂) * g₁⁻¹ ∈ K := K.mul_mem (K.mul_mem hg1 hA) (K.inv_mem hg1)
  refine fourClassesLarge_of_commBase K hL (fun z hz => ?_) baseAll
  interval_cases z
  · exact Or.inl ⟨hA, ha5⟩
  · exact Or.inl ⟨hB, hb5⟩
  · exact Or.inr htK
  · refine Or.inl ⟨K.inv_mem hA, ?_⟩
    change (g₂ * g₂)⁻¹ ^ 5 = 1
    rw [inv_pow, ha5, inv_one]
  · refine Or.inl ⟨K.inv_mem hB, ?_⟩
    change (g₁ * (g₂ * g₂) * g₁⁻¹)⁻¹ ^ 5 = 1
    rw [inv_pow, hb5, inv_one]

theorem fourClassesLarge_R1_centralizerIn (H : Subgroup (Equiv.Perm (Fin 3510)))
    (h1 : PRep 3510 12 G1 g₁) (h2 : PRep 3510 12 G2 g₂) (ht : PRep 3510 12 T t) (hg1 : g₁ ∈ H)
    (hg2 : g₂ ∈ H) : FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn H t) := by
  obtain ⟨c1, c2⟩ := comm_gens h1 h2 ht
  exact fourClassesLarge_R1 _ h1 h2 ht (CFSG.Sporadic.Schreier.mem_centralizerIn.2 ⟨hg1, c1⟩)
    (CFSG.Sporadic.Schreier.mem_centralizerIn.2 ⟨hg2, c2⟩)
    fun k hk => (CFSG.Sporadic.Schreier.mem_centralizerIn.1 hk).2

end CertificateChecks.KernelSpor.Fi22R1

end
