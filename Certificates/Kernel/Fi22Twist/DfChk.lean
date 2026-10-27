module

public import Certificates.Data.Kernel.Fi22Twist.Leaf
public import Certificates.Kernel.Fi22Twist.Data
public import Certificates.Kernel.Fi22Twist.DfText
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist

@[expose] noncomputable def ch431009df_ (k : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 9) k) (fun u =>
    dfK DF CertificateChecks.KernelFi22Twist.TX.F (Nat.div u (nat_lit 27)) (Nat.mod u (nat_lit 27)))
    (nat_lit 9)

end CertificateChecks.KernelFi22Twist

#kc_each CertificateChecks.KernelFi22Twist.ch431009df_ 0 15

end
