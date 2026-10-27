module

public import CFSG.Quasithin.H13.L32N1447Inputs
public import Certificates.Kernel.H13.PowP
public import Certificates.Kernel.H13.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.Q1447Cert CFSG.KC.Mat8P

@[expose] def kbY (p : ℕ) : Bool :=
  !(powP p 315 == oneP) || memLR (ofListLR (elemsF (conjOf s7Conj))) (unpackM p)

@[expose] noncomputable def kbChunk (k : ℕ) : Bool := ((D.s7L.drop (k * 240)).take 240).all kbY

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#kc_each kbChunk 0 21

end CertificateChecks.KernelH13

end
