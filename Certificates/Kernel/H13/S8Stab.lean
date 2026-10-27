module

public import CFSG.Quasithin.H13.L32NS8Inputs
public import Certificates.Data.Kernel.Mat8P
public import Certificates.Kernel.H13.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.KC.Mat8P

@[expose] def stabY (y : List ℕ) : Bool :=
  iiList.all fun v => !(mv8R y v == v) || (y.take 4).all (· < 16)

@[expose] noncomputable def stabChunk (k : ℕ) : Bool :=
  ((D.s8L.drop (k * 2016)).take 2016).all fun p => stabY (unpackM p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
#kc_each stabChunk 0 20

end CertificateChecks.KernelH13

end
