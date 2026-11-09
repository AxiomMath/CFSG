module

public import Certificates.Kernel.Sporadic.ON2.Data
public import CFSG.Certificates.Kernel.Spor.ONKWABSound

public section

namespace CertificateChecks.KernelSpor.ON2

@[expose] noncomputable def mvSW (s : Nat) : Bool :=
  CFSG.KS.ONW.mvRangeAB ONW.K ONW.LA ONW.LB ONW.A ONW.B (nat_lit 245520) (Nat.mul s (nat_lit 240))
    (nat_lit 240)

theorem mvS_of_W (s : Nat) (h : mvSW s = true) : mvS s = true := CFSG.KS.ONW.mvRangeAB_imp h

end CertificateChecks.KernelSpor.ON2

end
