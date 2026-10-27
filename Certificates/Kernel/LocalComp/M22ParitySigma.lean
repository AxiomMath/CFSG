module

public import Certificates.Kernel.LocalComp.M22Parity
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAutInputs

public section

namespace CertificateChecks.KernelLC

open Equiv Equiv.Perm CFSG.ComponentClassification.WittDesign

@[expose] def sigmaPerm : Perm (Fin 22) :=
  swap 4 8 * swap 5 21 * swap 6 20 * swap 7 13 * swap 9 19 * swap 11 15 * swap 16 18

theorem sigmaFun_eq (x : Fin 22) : sigmaFun x = sigmaPerm x := by
  fin_cases x <;> rfl

theorem sign_sigmaPerm : sign sigmaPerm = -1 := by
  simp [sigmaPerm, sign_swap]

theorem m22Count_sigma :
    m22Count (fun g => ∀ x, g x = sigmaFun x) = 0 := by
  rw [← card_m22_subtype, Nat.card_eq_zero]
  left
  refine ⟨fun ⟨g, hg⟩ => ?_⟩
  have he : (g : Perm (Fin 22)) = sigmaPerm := Equiv.ext fun x => by rw [hg x, sigmaFun_eq]
  have h1 := mem_alternatingGroup.mp (m22_le_alt g.2)
  rw [he, sign_sigmaPerm] at h1
  exact absurd h1 (by decide)

end CertificateChecks.KernelLC

end
