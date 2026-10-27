module

public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CertificateChecks.KernelLC.Slices

open CFSG.KC.Enum CFSG.KS

theorem join {f : Nat → Bool} {a b : Nat} (h1 : ∀ s < a, f s = true)
    (h2 : ∀ s < b, f (Nat.add a s) = true) : ∀ s < a + b, f s = true := by
  intro s hs
  by_cases h : s < a
  · exact h1 s h
  · have e := h2 (s - a) (by omega)
    have e2 : Nat.add a (s - a) = s := by change a + (s - a) = s; omega
    rwa [e2] at e

theorem of_slices {R : Nat → Bool} {K N S : Nat}
    (h : ∀ s < S, allBlk (Nat.mul K s) (fun j => bIf(Nat.blt j N, R j, true)) K = true)
    (hN : N ≤ K * S) : ∀ j < N, R j = true := by
  intro j hj
  have hK : 0 < K := Nat.pos_of_ne_zero fun e => by subst e; omega
  have hs : j / K < S := by
    rw [Nat.div_lt_iff_lt_mul hK, Nat.mul_comm]
    omega
  have e := allBlk_spec (h (j / K) hs) (j % K) (Nat.mod_lt _ hK)
  have e2 : Nat.add (Nat.mul K (j / K)) (j % K) = j := Nat.div_add_mod j K
  rw [e2, Nat.blt_eq.mpr hj] at e
  exact e

end CertificateChecks.KernelLC.Slices

end
