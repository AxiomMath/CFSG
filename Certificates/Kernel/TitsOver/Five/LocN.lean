module

public import Certificates.Kernel.TitsOver.Five.LocEnum
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum

theorem cn_sl0 : penumSlK 1755 11 (mask 11) (1755 * 11) false CNE.G CNE.GI CNE.k CNE.cnt CNE.T
    CNE.PL CNE.POS CNE.SRT CNE.SRI 0 100 = true := by quickRfl
theorem cn_sl100 : penumSlK 1755 11 (mask 11) (1755 * 11) false CNE.G CNE.GI CNE.k CNE.cnt CNE.T
    CNE.PL CNE.POS CNE.SRT CNE.SRI 100 100 = true := by quickRfl
theorem cn_sl200 : penumSlK 1755 11 (mask 11) (1755 * 11) false CNE.G CNE.GI CNE.k CNE.cnt CNE.T
    CNE.PL CNE.POS CNE.SRT CNE.SRI 200 100 = true := by quickRfl

end CertificateChecks.KernelTitsOver.Five

end
