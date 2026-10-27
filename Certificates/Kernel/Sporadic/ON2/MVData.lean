module

public import Certificates.Kernel.Sporadic.ON2.Data
public import Certificates.Kernel.Sporadic.ON.MVData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON2

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONF CertificateChecks.KernelSpor.ON

theorem colsOKA : colsOK ONW.LA = true := by decide +kernel
theorem colsOKB : colsOK ONW.LB = true := by decide +kernel
theorem flatWA : (ONFA.CS.flatten == ONW.LA) = true := by decide +kernel
theorem flatWB : (ONFB.CS.flatten == ONW.LB) = true := by decide +kernel

@[expose] noncomputable def mvSF (s : Nat) : Bool :=
  mvRangeF ONW.K ONFA.T ONFB.T (nat_lit 39) ONW.A ONW.B (nat_lit 245520) (Nat.mul s (nat_lit 240))
    (nat_lit 240)

theorem mvS_of_F (s : Nat) (h : mvSF s = true) : mvS s = true :=
  mvRangeF_imp tabA lensA colsOKA flatWA lenA tabB lensB colsOKB flatWB lenB h

end CertificateChecks.KernelSpor.ON2

end
