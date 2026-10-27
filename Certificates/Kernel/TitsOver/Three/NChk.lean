module

public import Certificates.Kernel.TitsOver.Three.Enum
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem n_sl0 : penumSlK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 0 108 = true := by quickRfl
theorem n_sl108 : penumSlK 1755 11 (mask 11) (1755 * 11) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 108 108 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
