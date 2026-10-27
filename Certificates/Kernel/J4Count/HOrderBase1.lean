
module


public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.J4SNoCompData
public import CFSG.Sporadic.Schreier.J4SOrderBase1
public import Certificates.Kernel.J4Hub.Card

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2

theorem card_N_mul_card_K_le : Nat.card N * Nat.card K ≤ Nat.card H := by
  have : Finite J := CertificateChecks.KernelJ4Hub.finite_J
  have hf : Function.Injective (fun p : N × K =>
      (⟨(p.1 : J) * (p.2 : J), H.mul_mem (N_le_H p.1.2) (K_le_H p.2.2)⟩ : H)) := by
    intro p q e
    beta_reduce at e
    have e' : (p.1 : J) * (p.2 : J) = (q.1 : J) * (q.2 : J) := Subtype.mk.inj e
    have hmem : (q.1 : J)⁻¹ * (p.1 : J) ∈ K ⊓ N := by
      refine ⟨?_, N.mul_mem (N.inv_mem q.1.2) p.1.2⟩
      have h1 : (q.1 : J)⁻¹ * (p.1 : J) = (q.2 : J) * (p.2 : J)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e', mul_inv_cancel_right]
      rw [h1]
      exact K.mul_mem q.2.2 (K.inv_mem p.2.2)
    rw [K_inf_N, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have h2 : (p.2 : J) = q.2 := by
      rw [← hmem] at e'
      exact mul_left_cancel e'
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext h2)
  have h := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_prod] at h

end CertificateChecks.KernelJ4Count

end
