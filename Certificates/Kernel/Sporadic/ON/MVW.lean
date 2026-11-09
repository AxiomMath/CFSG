module

public import Certificates.Kernel.Sporadic.ON.Data
public import CFSG.Certificates.Kernel.Spor.ONKWABSound

public section

namespace CertificateChecks.KernelSpor.ON

open CFSG.KS.ONW

@[expose] noncomputable def mvSW (s : Nat) : Bool :=
  mvRangeAB ONV.K ONV.LA ONV.LB ONV.A ONV.B (nat_lit 245520) (Nat.mul s (nat_lit 240)) (nat_lit 240)

theorem mvS_of_W (s : Nat) (h : mvSW s = true) : mvS s = true := mvRangeAB_imp h

end CertificateChecks.KernelSpor.ON

end
