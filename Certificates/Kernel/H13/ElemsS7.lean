module

public import CFSG.Quasithin.H13.L32NS7Inputs
public import CFSG.Certificates.Kernel.Mat8PSound
public import Certificates.Kernel.H13.Data
public import Certificates.Kernel.H13.BfsS8

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.KC.Mat8P CFSG.KC.Mat8T

theorem s7L_eq : elemsP (CFSG.Quasithin.H13.S7Cert.s7G.map code64R) = D.s7L := by
  rw [elemsP_eq_T 16 65521, bfsS7_bfs]

theorem s7E_eq : CFSG.Quasithin.H13.S7Cert.s7E = D.s7L.map unpackM := by
  rw [CFSG.Quasithin.H13.S7Cert.s7E, elemsOf_eqP _ (by decide), s7L_eq]

end CertificateChecks.KernelH13

end
