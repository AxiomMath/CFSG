module

public import Certificates.Kernel.Sporadic.ONEN.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.ONCheckAuxInputs
public import Certificates.Kernel.Sporadic.ON.Seven

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONEN

open CFSG.KS.TW CFSG.ONSchreier CertificateChecks.KernelSpor.ONS
open CertificateChecks.KernelSpor.ON (TT)

theorem ch13790A_0 : ch13790A 0 = true := by quickRfl

theorem ch13790A_1 : ch13790A 227759 = true := by quickRfl

theorem ch13790A_2 : ch13790A 100817 = true := by quickRfl

theorem ch13790E_0 : (ch13790E 0 0 && ch13790E 0 227759 && ch13790E 0 100817) = true := by
  quickRfl

theorem ch13790E_1 : (ch13790E 1 0 && ch13790E 1 227759 && ch13790E 1 100817) = true := by
  quickRfl

theorem ch13790D_ok : (ch13790D 0 && ch13790D 1) = true := by quickRfl

theorem ch13790N_0 : (ch13790N 0 0 && ch13790N 0 1 && ch13790N 0 2) = true := by quickRfl

theorem ch13790N_1 : (ch13790N 1 0 && ch13790N 1 1 && ch13790N 1 2) = true := by quickRfl

theorem ch13790N_2 : (ch13790N 2 0 && ch13790N 2 1 && ch13790N 2 2) = true := by quickRfl

theorem ch13790N_3 : (ch13790N 3 0 && ch13790N 3 1 && ch13790N 3 2) = true := by quickRfl

end CertificateChecks.KernelSpor.ONEN

end
