module

public import Certificates.Kernel.W4C2.Data
public import CFSG.Certificates.Kernel.Common.Each

public section

namespace CertificateChecks.KernelW4C2

open CFSG.KC.W4C2K

@[expose] noncomputable def ch330390val (i : Nat) : Bool :=
  (GL.getD i []).all fun n => validK (mk n (dualK n) false)

#kc_each ch330390val 0 16

end CertificateChecks.KernelW4C2
