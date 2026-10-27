module

public import Certificates.Data.Kernel.Misc.RuScanE
public import Certificates.Kernel.Misc.RuScan.DataL
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan
open CFSG.KLie.CT (notB)

theorem ch7230lb0 : lbK V0 136 = true := by quickRfl
theorem ch7230lb1 : lbK V1 80 = true := by quickRfl
theorem ch7230lb2 : lbK V2 16 = true := by quickRfl
theorem ch7230lb3 : lbK V3 24 = true := by quickRfl
theorem ch7230lb8 : lbK V8 6 = true := by quickRfl

theorem ch7230lbNeg : notB (lbK V0 135) = true := by quickRfl

end CertificateChecks.KernelMisc.RuScan

end
