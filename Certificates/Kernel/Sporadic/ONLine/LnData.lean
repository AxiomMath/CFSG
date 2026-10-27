module

public import Certificates.Kernel.Sporadic.ONLine.Data
public import Certificates.Kernel.Sporadic.ON.MVData
public import CFSG.Certificates.Kernel.Spor.ONLineKFSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONLine

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONF CertificateChecks.KernelSpor.ON

@[expose] noncomputable def lnSF (s : Nat) : Bool :=
  lineRangeF ONL.K ONL.LP ONFA.T ONFB.T (nat_lit 39) ONL.A ONL.B (nat_lit 122760)
    (Nat.mul s (nat_lit 120)) (nat_lit 120)

theorem lnS_of_F (s : Nat) (h : lnSF s = true) : lnS s = true :=
  lineRangeF_imp tabA lensA colsA flatA lenA tabB lensB colsB flatB lenB h

end CertificateChecks.KernelSpor.ONLine

end
