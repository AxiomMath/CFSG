module

public import Certificates.Data.Kernel.Misc.RuBigZFix
public import Certificates.Kernel.SporSch.Ru.CData
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Misc.RuBigZ CertificateChecks.KernelSporSch
open CFSG.KLie.CT (notB)

theorem ch7233fx_ok :
    (fixL RuCS.LR RuCS.TR 1 0 && fixL RuCS.LR RuCS.TR 2 0) = true := by quickRfl

theorem ch7233fx_neg : notB (fixL RuCS.LR RuCS.TR 0 0) = true := by quickRfl

end CertificateChecks.KernelMisc.RuBigZ

end
