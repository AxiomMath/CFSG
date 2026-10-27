module

public import Certificates.Kernel.G24Cls.Chk26992
public import Certificates.Kernel.G24Cls.C27203
public import CFSG.Certificates.Kernel.G24WordSound

public section

set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelG24.Dih26992

open CFSG.KC.Enum CFSG.KC.G24Key CFSG.KC.G24Word CertificateChecks.KernelG24.Tri27206
  CertificateChecks.KernelG24.Cls27203 CFSG.EvenSporadicStandard.G24Aut CFSG.Monster.B.Co2
  CFSG.Sporadic.Co1Block


theorem gGen0 : gGen 1 0 = xBar := by simp [gGen]

theorem gGen1 : gGen 1 1 = yBar := by simp [gGen]

theorem ptX : PtRep (LC.S 0) xBar := by
  have h : PtRep (LC.S 0) (gGen 1 0) := ptLC (by norm_num)
  rwa [gGen0] at h

theorem ptY : PtRep (LC.S 1) yBar := by
  have h : PtRep (LC.S 1) (gGen 1 1) := ptLC (by norm_num)
  rwa [gGen1] at h

theorem ptXI : PtRep (LC.SI 0) xBar⁻¹ := by
  have h : PtRep (LC.SI 0) (gGen 1 0)⁻¹ := ptSI 0
  rwa [gGen0] at h

theorem ptYI : PtRep (LC.SI 1) yBar⁻¹ := by
  have h : PtRep (LC.SI 1) (gGen 1 1)⁻¹ := ptSI 1
  rwa [gGen1] at h

theorem ptL (c : ℕ) : PtRep (letC (LC.S 0) (LC.SI 0) (LC.S 1) (LC.SI 1) c) (letE xBar yBar c) :=
  letC_pt ptX ptXI ptY ptYI c

theorem ptLI (c : ℕ) :
    PtRep (letC (LC.SI 0) (LC.S 0) (LC.SI 1) (LC.S 1) c) (letE xBar yBar c)⁻¹ :=
  letC_pt_inv ptX ptXI ptY ptYI c

theorem hxD : xBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert _ _)

theorem hyD : yBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem d8_facts : ∃ u ∈ twoBD, ∃ v ∈ twoBD,
    u * u = 1 ∧ v * v = 1 ∧ (u * v) ^ 4 = 1 ∧ u * v ≠ v * u := by
  have k := kD8
  simp only [Bool.and_eq_true] at k
  obtain ⟨⟨⟨⟨⟨-, -⟩, k2⟩, k3⟩, k4⟩, k5⟩ := k
  have one : ∀ w, fixB L26 w = true → wordL xBar yBar w = 1 := fun w h => by
    obtain ⟨h0, h1, h2⟩ := fixB_spec ptL h
    exact twoBD_eq_one (wordL_mem hxD hyD w) h0 h1 h2
  refine ⟨wordL xBar yBar u26, wordL_mem hxD hyD _, wordL xBar yBar v26, wordL_mem hxD hyD _,
    ?_, ?_, ?_, ?_⟩
  · rw [← wordL_append]
    exact one _ k2
  · rw [← wordL_append]
    exact one _ k3
  · rw [pow_succ, pow_succ, pow_succ, pow_one, ← wordL_append, ← wordL_append, ← wordL_append,
      ← wordL_append]
    exact one _ k4
  · rw [← wordL_append, ← wordL_append]
    exact diffB_spec ptL (by norm_num) k5

theorem d8_ok : ∃ u ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
    ∃ v ∈ Subgroup.closure {permOfArr 1365 xa, permOfArr 1365 ya},
      u * u = 1 ∧ v * v = 1 ∧ (u * v) ^ 4 = 1 ∧ u * v ≠ v * u := by
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY]
  exact d8_facts

end CertificateChecks.KernelG24.Dih26992

end
