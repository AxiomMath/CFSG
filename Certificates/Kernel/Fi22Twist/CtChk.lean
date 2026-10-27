module

public import Certificates.Data.Kernel.Fi22Twist.Ct
public import Certificates.Kernel.Fi22Twist.Sift
public import Certificates.Kernel.Sporadic.Fi22.E2067T
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist

@[expose] noncomputable def ctI (u : Nat) : Nat :=
  nIf(Nat.blt u (nat_lit 3), nat_lit 21, nIf(Nat.blt u (nat_lit 6), nat_lit 22, nat_lit 23))

@[expose] noncomputable def ch431009ct (u : Nat) : Bool :=
  ctK (sfG (Nat.add (nat_lit 23) u)) (CertificateChecks.KernelSpor.Fi22ExtT.L (ctI u))

end CFSG.KD.Fi22Twist

#kc_each CFSG.KD.Fi22Twist.ch431009ct 0 11

namespace CFSG.KD.Fi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist

theorem neg431009ct : Bool.not (ctK (sfG (nat_lit 23)) (CertificateChecks.KernelSpor.Fi22ExtT.L 22)) =
    true := by
  quickRfl

end CFSG.KD.Fi22Twist

end
