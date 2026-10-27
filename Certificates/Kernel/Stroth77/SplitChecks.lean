module

public import Certificates.Kernel.Stroth77.SplitData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSplit778711

open CFSG.KC.Stroth77SP

theorem ch778711_tab : tabOK tabs = true := by quickRfl
theorem ch778711_cl : clOK tabs = true := by quickRfl
theorem ch778711_a : aOK tabs = true := by quickRfl
theorem ch778711_ad : adOK tabs = true := by quickRfl
theorem ch778711_s1 : s1OK tabs = true := by quickRfl
theorem ch778711_echar : eCharOK tabs = true := by quickRfl
theorem ch778711_red : redOK tabs = true := by quickRfl
theorem ch778711_sg : sgOK tabs = true := by quickRfl
theorem ch778711_uv : actS tabs 4 1 2 6 9 19 = true := by quickRfl
theorem ch778711_t : actS tabs 8 1 2 5 11 17 = true := by quickRfl
theorem ch778711_u : actS tabs 64 2 1 8 4 16 = true := by quickRfl
theorem ch778711_rho : actF tabs rhoK 2 3 8 12 16 = true := by quickRfl

end CertificateChecks.KernelSplit778711
