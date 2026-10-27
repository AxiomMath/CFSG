
module

public import Certificates.Kernel.Sporadic.Fi22.S3147Base

public import CFSG.Monster.B.Fischer.Fi22Faithful

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSpor.Fi22S

open CFSG.Certificates CFSG.Monster.B.Fischer

theorem fi22P_formSep
    {σ : Equiv.Perm (Fin 3510)} (hσ : σ ∈ fi22P)
    (hfix : ∀ r ∈ fi22CentralizerIdx, ∀ h : r < 3510, σ ⟨r, h⟩ = ⟨r, h⟩) : σ = 1 := by
  rw [← fi22Rho_range] at hσ
  obtain ⟨g, rfl⟩ := hσ
  have hGB : fi22G ≤ glFormPreserving fi22Bil :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact fi22Bil_seed i)
  have hGdet : fi22G ≤ glDetOne :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨i, rfl⟩
      exact (mem_glDetOne _).2 (det_fi22SeedLin i))
  have hq : ∀ s : fi22S, glPullback (g : Fi22GL) s.1 = s.1 := by
    rintro ⟨_, r, hr, rfl⟩
    have hr' : r < 3510 := by
      simp only [fi22CentralizerIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
      omega
    have h := fi22Form_rho g ⟨r, hr'⟩
    rw [hfix r hr hr'] at h
    exact h.symm
  obtain ⟨c, hc⟩ := eq_smul_id_of_pullback_eq (ι := fi22S) fi22Bil_nondegenerate (hGB g.2)
    (q := fun s => s.1) (β := fun s => fi22Beta s.1)
    (fun s => fi22Beta_apply (fi22S_subset s.2))
    (T := fun s => fi22TLin s.1) (fun s => fi22TLin_spec s.1 s.2)
    (by rw [← fi22_centralizer]; ext M; simp) hq
  have hdetg := (mem_glDetOne _).1 (hGdet g.2)
  rw [hc, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdetg
  rw [fi22_hroot c hdetg, one_smul] at hc
  have hg : g = 1 := Subtype.ext (Units.ext hc)
  rw [hg, map_one]

end CertificateChecks.KernelSpor.Fi22S

end
