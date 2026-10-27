module

public import Certificates.Kernel.U43Mod.Sound

public section

namespace CertificateChecks.KernelU43Mod

open CFSG.LieType.Multipliers.U43 CFSG.EvenSporadicStandard.M24Std.CU43


theorem psi_mem_P (g : X₀) : psi g ∈ P := by
  have hg : g ∈ Subgroup.closure ({xElt, yElt} : Set X₀) := by
    rw [closure_xy]
    exact Subgroup.mem_top g
  have h := Subgroup.mem_map_of_mem psi hg
  rw [MonoidHom.map_closure, Set.image_pair] at h
  rw [P_eq_closure]
  exact h

theorem psi_sep (g h : X₀) (e0 : psi g ⟨0, by norm_num⟩ = psi h ⟨0, by norm_num⟩)
    (e1 : psi g ⟨1, by norm_num⟩ = psi h ⟨1, by norm_num⟩)
    (e9 : psi g ⟨9, by norm_num⟩ = psi h ⟨9, by norm_num⟩) : g = h := by
  refine psi_injective (eq_of_base (psi_mem_P g) (psi_mem_P h) fun p hp => ?_)
  simp only [bs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact e0
  · exact e1
  · exact e9

end CertificateChecks.KernelU43Mod

end
