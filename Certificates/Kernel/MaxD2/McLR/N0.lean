module

public import Certificates.Kernel.MaxD2.McLR.Enum
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem n_sl0 : penumSlK 275 9 (mask 9) (275 * 9) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 0 500 = true := by quickRfl

theorem n_sl500 : penumSlK 275 9 (mask 9) (275 * 9) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 500 500 = true := by quickRfl

theorem n_sl1000 : penumSlK 275 9 (mask 9) (275 * 9) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 1000 500 = true := by quickRfl

theorem n_sl1500 : penumSlK 275 9 (mask 9) (275 * 9) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 1500 500 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLR

end
