module

public import Certificates.Data.Kernel.Fi22Twist.Tf
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Sporadic.Fi22.X2069PT
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def ch431009tf_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 8) k) (fun f =>
    bIf(Nat.blt f (nat_lit 865), tfK TF TT CertificateChecks.KernelSpor.Fi22ChT.F f, true))
    (nat_lit 8)

end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009tf_ 0 109

end
