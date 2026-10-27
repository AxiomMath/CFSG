module

public import Certificates.Kernel.W4C2.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelW4C2

open CFSG.KC.W4C2K

@[expose] noncomputable def ch330390inj (i : Nat) : Bool :=
  (List.range' (4096 * i) 4096).filter injK == GL.getD i []

#kc_each ch330390inj 0 16

end CertificateChecks.KernelW4C2
