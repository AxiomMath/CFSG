module

public import Certificates.Kernel.Sporadic.OddCore.HL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt

theorem kE84 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 37800 450 = true := by quickRfl
theorem kE85 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 38250 450 = true := by quickRfl
theorem kE86 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 38700 450 = true := by quickRfl
theorem kE87 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 39150 450 = true := by quickRfl
theorem kE88 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 39600 450 = true := by quickRfl
theorem kE89 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 40050 450 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
