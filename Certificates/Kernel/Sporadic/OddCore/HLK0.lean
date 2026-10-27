module

public import Certificates.Kernel.Sporadic.OddCore.HL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt

theorem kE0 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 0 450 = true := by quickRfl
theorem kE1 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 450 450 = true := by quickRfl
theorem kE2 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 900 450 = true := by quickRfl
theorem kE3 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 1350 450 = true := by quickRfl
theorem kE4 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 1800 450 = true := by quickRfl
theorem kE5 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 2250 450 = true := by quickRfl
theorem kE6 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 2700 450 = true := by quickRfl
theorem kE7 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 3150 450 = true := by quickRfl
theorem kE8 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 3600 450 = true := by quickRfl
theorem kE9 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 4050 450 = true := by quickRfl
theorem kE10 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 4500 450 = true := by quickRfl
theorem kE11 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 4950 450 = true := by quickRfl
theorem kE12 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 5400 450 = true := by quickRfl
theorem kE13 : penumSlK 105 7 (mask 7) (105 * 7) false HKE.G HKE.GI 9 HKE.cnt
    HKE.T HKE.PL HKE.POS HKE.SRT HKE.SRI 5850 450 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
