module

public import Certificates.Kernel.Sporadic.ONLine.Data
public import Certificates.Kernel.Sporadic.ON.GenF
public import CFSG.Certificates.Kernel.Spor.ONLineKWSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONLine

@[expose] noncomputable def lnSW (s : Nat) : Bool :=
  CFSG.KS.ONW.lineRangeW ONL.K ONL.LP ONV.LA ONV.LB ONL.A ONL.B (nat_lit 122760)
    (Nat.mul s (nat_lit 120)) (nat_lit 120)

theorem lnS_of_W (s : Nat) (h : lnSW s = true) : lnS s = true := CFSG.KS.ONW.lineRangeW_imp h

end CertificateChecks.KernelSpor.ONLine

end
