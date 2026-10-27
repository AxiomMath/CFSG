
module

public import Certificates.Kernel.ThCent.ContractBase

public import Certificates.Kernel.ThCent.Consumers

public section

namespace CertificateChecks.KernelThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Kernel CFSG.Sporadic.Bridge CFSG.KC.Th CFSG.KC.ThCent
  CFSG.KC.Th.Spec CFSG.KC.Th.Spec.DceStr CFSG.KD CFSG.KD.ThCent TauCeti

variable (h : KernelFacts)
include h

theorem exists_cent7 :
    ∃ z : J, orderOf z = 7 ∧ Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 1176 := by
  refine ⟨_, ?_, card_centralizer_x7y7_le h⟩
  have := h.finite
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ, hx, hA, hB, hBi, hk⟩ := psi h
  obtain ⟨-, hpow, h1, -, -, -⟩ := class_T (card_P_eq h) (hKc h).le C7A.misc C7A.diff.all
    C7A.sel.all C7A.comm.all C7A.or1.all C7A.or2.all C7A.or3.all C7A.or4.all C7A.or5.all
    C7A.or6.all C7A.or7.all C7A.or8.all C7A.or9.all C7A.or10.all
  obtain ⟨c, hc⟩ := conj_wit h hx hA hB hBi hk W.w7A W.d7A _ mat_z7
  rw [SemiconjBy.orderOf_eq _ hc]
  have hy7 : ψ (wval gen C7A.word) ^ 7 = 1 := by
    have e : wval gen C7A.word ^ 7 = 1 := hpow
    rw [← map_pow, e, map_one]
  have hy1 : ψ (wval gen C7A.word) ≠ 1 := by
    intro e
    have e2 : wval gen C7A.word = 1 := hψ.1 (e.trans (map_one ψ).symm)
    exact absurd (h1 e2) (by decide +kernel)
  exact orderOf_eq_prime hy7 hy1

end CertificateChecks.KernelThCent

end
