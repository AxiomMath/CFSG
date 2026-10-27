module

public import Certificates.Kernel.MaxD2.HSOver.Enum
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.HSOver

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem n_sl1000 : penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 1000 1000 = true := by quickRfl

theorem n_sl2000 : penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 2000 1000 = true := by quickRfl

theorem n_sl3000 : penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 3000 1000 = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSOver

end
