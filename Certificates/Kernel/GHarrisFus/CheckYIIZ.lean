module

public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.KC.GHFus CFSG.KD.GHFus

theorem ch22609yIIZ_r0 : fusRange dmT mvT CT L yIIZ goodNoneK 0 11 = true := by quickRfl
theorem ch22609yIIZ_r1 : fusRange dmT mvT CT L yIIZ goodNoneK 11 22 = true := by quickRfl
theorem ch22609yIIZ_r2 : fusRange dmT mvT CT L yIIZ goodNoneK 22 33 = true := by quickRfl
theorem ch22609yIIZ_r3 : fusRange dmT mvT CT L yIIZ goodNoneK 33 44 = true := by quickRfl
theorem ch22609yIIZ_r4 : fusRange dmT mvT CT L yIIZ goodNoneK 44 55 = true := by quickRfl
theorem ch22609yIIZ_r5 : fusRange dmT mvT CT L yIIZ goodNoneK 55 66 = true := by quickRfl
theorem ch22609yIIZ_r6 : fusRange dmT mvT CT L yIIZ goodNoneK 66 77 = true := by quickRfl
theorem ch22609yIIZ_r7 : fusRange dmT mvT CT L yIIZ goodNoneK 77 87 = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
