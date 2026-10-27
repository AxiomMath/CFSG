
module

public import Certificates.Kernel.L34W.Two
public import Certificates.Kernel.L34W.Glue
public import CFSG.Certificates.Kernel.L34W.ModKSound
public import CFSG.Certificates.Kernel.L34W.OuterSound

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

theorem mem_kbMasks_getD : ∀ m ∈ kbMasks, ∃ k < 15, kbMasks.getD k 0 = m := by decide

theorem two_spec : ∀ kb ∈ kbList,
    ∃ x₁ ∈ allM, ∃ x₂ ∈ allM, ∃ x₃ ∈ allM, ∃ x₄ ∈ allM,
      isInvKB kb x₁ = true ∧ isInvKB kb x₂ = true ∧ isInvKB kb x₃ = true ∧
      isInvKB kb x₄ = true ∧ eqKB kb x₂ x₁ = false ∧ commKB kb x₁ x₂ = true ∧
      commKB kb x₃ x₁ = true ∧ commKB kb x₃ x₂ = true ∧ commKB kb x₄ x₁ = true ∧
      commKB kb x₄ x₂ = true ∧ commKB kb x₃ x₄ = false := by
  intro kb hkb
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hkb
  obtain ⟨k, hk, e⟩ := mem_kbMasks_getD m hm
  have h := allN_spec two_k k hk
  rw [strictB_eq, e] at h
  exact twoC_spec t1Of h

end CertificateChecks.KernelL34W

end
