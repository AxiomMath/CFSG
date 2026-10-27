module

public import Certificates.Data.Kernel.Fi22Twist.Dj
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Fi22Twist.DfText
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def ch431009dj_ (j : Nat) : Bool :=
  djK DF CertificateChecks.KernelFi22Twist.TX.F j

end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009dj_ 0 5

end
