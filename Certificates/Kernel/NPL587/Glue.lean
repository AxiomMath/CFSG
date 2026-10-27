module

public import Certificates.Kernel.NPL587.Checks
public import CFSG.Certificates.Kernel.NPL587KSound

public section

namespace CertificateChecks.KernelNPL587

open CFSG.Quasithin.H13.NPLKSound CFSG.KD.NPL587 CFSG.KD.NPL587.Chk

theorem facts : Nat.card S0K = 64 ∧ ∀ σ : Equiv.Perm (Fin 8), σ ≠ 1 → (σ ^ 5 = 1 ∨ σ ^ 7 = 1) →
    448 < Nat.card (Subgroup.closure (insert σ (S0K : Set (Equiv.Perm (Fin 8))))) := by
  have c16 : (∀ p ∈ ([] : List (ℕ × ℕ)), p.1 ∈ qc ∧ p.2 ∈ s0) ∧
      CFSG.Quasithin.H13.NPLK.incB (bnd.getD 16 0)
        (([] : List (ℕ × ℕ)).map fun p => CFSG.Quasithin.H13.NPLK.tauC p.1 p.2) = true :=
    ⟨by simp, rfl⟩
  have c15 := covOK_cons cov_ok15 c16
  have c14 := covOK_cons cov_ok14 c15
  have c13 := covOK_cons cov_ok13 c14
  have c12 := covOK_cons cov_ok12 c13
  have c11 := covOK_cons cov_ok11 c12
  have c10 := covOK_cons cov_ok10 c11
  have c9 := covOK_cons cov_ok9 c10
  have c8 := covOK_cons cov_ok8 c9
  have c7 := covOK_cons cov_ok7 c8
  have c6 := covOK_cons cov_ok6 c7
  have c5 := covOK_cons cov_ok5 c6
  have c4 := covOK_cons cov_ok4 c5
  have c3 := covOK_cons cov_ok3 c4
  have c2 := covOK_cons cov_ok2 c3
  have c1 := covOK_cons cov_ok1 c2
  have c0 := covOK_cons cov_ok0 c1
  have hlen := len_ok
  rw [beq_iff_eq] at hlen
  refine sound s0_ok reps_ok repc_ok ql_ok qc_ok c0.1 c0.2 ?_
  simp only [List.length_append, List.length_nil]
  omega

end CertificateChecks.KernelNPL587

end
