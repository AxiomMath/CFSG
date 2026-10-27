module

public import Certificates.Kernel.MaxD2.TitsA.Enum
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.TitsA

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem n_sl2200 : penumSlK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 2200 100 = true := by quickRfl

theorem n_sl2300 : penumSlK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 2300 100 = true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsA

end
