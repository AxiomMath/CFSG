module

public import Certificates.Kernel.Sporadic.OddCore.HL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt

theorem kE14 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 6300 450 = true := by quickRfl
theorem kE15 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 6750 450 = true := by quickRfl
theorem kE16 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 7200 450 = true := by quickRfl
theorem kE17 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 7650 450 = true := by quickRfl
theorem kE18 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 8100 450 = true := by quickRfl
theorem kE19 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 8550 450 = true := by quickRfl
theorem kE20 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 9000 450 = true := by quickRfl
theorem kE21 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 9450 450 = true := by quickRfl
theorem kE22 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 9900 450 = true := by quickRfl
theorem kE23 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 10350 450 = true := by quickRfl
theorem kE24 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 10800 450 = true := by quickRfl
theorem kE25 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 11250 450 = true := by quickRfl
theorem kE26 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 11700 450 = true := by quickRfl
theorem kE27 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 12150 450 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
