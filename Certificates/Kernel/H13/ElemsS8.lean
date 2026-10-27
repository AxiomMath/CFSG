module

public import CFSG.Quasithin.H13.L32NS8Inputs
public import CFSG.Certificates.Kernel.Mat8PSound
public import Certificates.Kernel.H13.Data

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8L_eq :
    elemsP (CFSG.Quasithin.H13.S8Cert.s8G.map code64R) = D.s8L := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s8L_lt : ∀ p ∈ D.s8L, p < 2 ^ 64 := by decide +kernel

theorem s8E_eq : CFSG.Quasithin.H13.S8Cert.s8E = D.s8L.map unpackM := by
  rw [CFSG.Quasithin.H13.S8Cert.s8E, elemsOf_eqP _ (by decide), s8L_eq]

end CertificateChecks.KernelH13

end
