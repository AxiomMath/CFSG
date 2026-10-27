module

public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.KC.GHFus CFSG.KD.GHFus

theorem ch22609bIZ_r0 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 0 11 = true := by quickRfl
theorem ch22609bIZ_r1 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 11 22 = true := by quickRfl
theorem ch22609bIZ_r2 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 22 33 = true := by quickRfl
theorem ch22609bIZ_r3 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 33 44 = true := by quickRfl
theorem ch22609bIZ_r4 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 44 55 = true := by quickRfl
theorem ch22609bIZ_r5 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 55 66 = true := by quickRfl
theorem ch22609bIZ_r6 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 66 77 = true := by quickRfl
theorem ch22609bIZ_r7 : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 77 87 = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
