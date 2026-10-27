module

public import CFSG.Quasithin.H13.L32NO3Inputs
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P

@[expose] def pow8F (x : List ℕ) (k : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) one8 (fun _ acc => mul8F x acc) k

theorem pow8_toF (x : List ℕ) : ∀ k, CFSG.Quasithin.H13.O3Cert.pow8 x k = pow8F x k
  | 0 => rfl
  | k + 1 => by
    rw [CFSG.Quasithin.H13.O3Cert.pow8, pow8_toF x k, mul8_toF]
    rfl

end CertificateChecks.KernelH13

end
