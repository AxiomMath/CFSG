module

public import CFSG.Quasithin.H13.L32NO3Inputs
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P

@[expose] def powP (p k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) oneP (fun _ acc => mulP p acc) k

theorem pow8_unpackM (p : ℕ) : ∀ k, CFSG.Quasithin.H13.O3Cert.pow8 (unpackM p) k = unpackM (powP p k)
  | 0 => oneP_eq.symm
  | k + 1 => by
    rw [CFSG.Quasithin.H13.O3Cert.pow8, pow8_unpackM p k, mul8_unpackM]
    rfl

theorem powP_lt (p : ℕ) : ∀ k, powP p k < 2 ^ 64
  | 0 => oneP_lt
  | k + 1 => mulP_lt p _

theorem pow8_beq_one (p k : ℕ) :
    (CFSG.Quasithin.H13.O3Cert.pow8 (unpackM p) k == one8) = (powP p k == oneP) := by
  rw [pow8_unpackM, ← oneP_eq, unpackM_beq (powP_lt p k) oneP_lt]

end CertificateChecks.KernelH13

end
