module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Kernel.Sporadic.Fi22.HypR1Glue

public section

namespace CertificateChecks.KernelSpor.Fi22CB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.Monster.B.Fischer
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier

@[expose] def letterPerm (h₁ h₂ t : Equiv.Perm (Fin 3510)) (z : ℕ) : Equiv.Perm (Fin 3510) :=
  [h₁, h₂, t, h₁⁻¹, h₂⁻¹].getD z 1

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

theorem fourClassesLarge_of_lettersOK
    {M : ℕ → ℕ} {T : ℕ} {t : Equiv.Perm (Fin 3510)} (ht : PRep 3510 12 T t)
    (hl : lettersOK M T = true) {B : List BaseRec} {PF ZF DF : ℕ}
    (hb : baseChk M B PF ZF DF = true) (H : Subgroup (Equiv.Perm (Fin 3510)))
    (hPH : fi22P ≤ H) : FourClassesLarge ↥(centralizerIn H t) := by
  simp only [lettersOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hl
  obtain ⟨hcn, e2, hp0, hp1, s0, s1, c0, c1, p0, p1⟩ := hl
  rw [allN_iff] at hcn
  obtain ⟨h₁, m1, r1⟩ := Fi22R1.exists_mem_P (hcn 0 (by norm_num)) hp0 s0
  obtain ⟨h₂, m2, r2⟩ := Fi22R1.exists_mem_P (hcn 1 (by norm_num)) hp1 s1
  have comm : ∀ {P : ℕ} {h : Equiv.Perm (Fin 3510)}, PRep 3510 12 P h →
      Fi22X.c P T = Fi22X.c T P → h * t = t * h := fun hP e =>
    prep_unique (prep_c hP ht) (by rw [e]; exact prep_c ht hP)
  have k1 : h₁ ∈ centralizerIn H t := mem_centralizerIn.2 ⟨hPH m1, comm r1 c0⟩
  have k2 : h₂ ∈ centralizerIn H t := mem_centralizerIn.2 ⟨hPH m2, comm r2 c1⟩
  have o1 := pow5_eq_one r1 p0
  have o2 := pow5_eq_one r2 p1
  have hL : ∀ z < 5, PRep 3510 12 (M z) (letterPerm h₁ h₂ t z) := by
    intro z hz
    interval_cases z
    · exact r1
    · exact r2
    · rw [e2]
      exact ht
    · exact prep_inv_of_permOK r1 hp0
    · exact prep_inv_of_permOK r2 hp1
  refine fourClassesLarge_of_commBase _ hL (fun z hz => ?_) hb
  interval_cases z
  · exact Or.inl ⟨k1, o1⟩
  · exact Or.inl ⟨k2, o2⟩
  · exact Or.inr fun k hk => (mem_centralizerIn.1 hk).2
  · refine Or.inl ⟨Subgroup.inv_mem _ k1, ?_⟩
    change h₁⁻¹ ^ 5 = 1
    rw [inv_pow, o1, inv_one]
  · refine Or.inl ⟨Subgroup.inv_mem _ k2, ?_⟩
    change h₂⁻¹ ^ 5 = 1
    rw [inv_pow, o2, inv_one]

end CertificateChecks.KernelSpor.Fi22CB

end
