module

public import Certificates.Kernel.GHarrisFus.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.KC.GHFus CFSG.KD.GHFus

theorem ch22609rows : rowsOK dmT mvT L L = true := by quickRfl
theorem ch22609invs : invsOK dmT mvT L = true := by quickRfl

theorem ch22608aT : fusRange dmT mvT CT L aT goodNoneK 0 87 = true := by quickRfl
theorem ch22608aA1L : fusRange dmT mvT CT L aA1L goodNoneK 0 87 = true := by quickRfl
theorem ch22608aZ0 : fusRange dmT mvT CT L aZ (goodAZK dmT mvT CT aZ.2.2.2.1 aZx aZwit) 0 44 = true := by
  quickRfl
theorem ch22608aZ1 : fusRange dmT mvT CT L aZ (goodAZK dmT mvT CT aZ.2.2.2.1 aZx aZwit) 44 87 = true := by
  quickRfl
theorem ch22608aA34 :
    fusRange dmT mvT CT L aA34 (goodA34K dmT mvT CT aA34.2.2.2.1 aA34x aA34wit) 0 87 = true := by
  quickRfl

theorem ch22609yIX : fusRange dmT mvT CT L yIX (goodFixZK dmT mvT) 0 87 = true := by quickRfl
theorem ch22609bIA1L : fusRange dmT mvT CT L bIA1L goodNoneK 0 87 = true := by quickRfl
theorem ch22609bIX : fusRange dmT mvT CT L bIX goodNoneK 0 87 = true := by quickRfl
theorem ch22609bIIA1L : fusRange dmT mvT CT L bIIA1L goodNoneK 0 87 = true := by quickRfl
theorem ch22609bIIX : fusRange dmT mvT CT L bIIX goodNoneK 0 87 = true := by quickRfl
theorem ch22609bIIA34 : fusRange dmT mvT CT L bIIA34 (goodFixZK dmT mvT) 0 87 = true := by quickRfl
theorem ch22609yIIA34 : fusRange dmT mvT CT L yIIA34 goodNoneK 0 87 = true := by quickRfl
theorem ch22609yIIX : fusRange dmT mvT CT L yIIX (goodFixZK dmT mvT) 0 87 = true := by quickRfl

end CertificateChecks.KernelGHarrisFus
