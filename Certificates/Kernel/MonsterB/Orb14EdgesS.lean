module

public import Certificates.Data.Kernel.MonsterB.Orb14
public import Certificates.Kernel.MonsterB.Orb14Net
public import Certificates.Kernel.MonsterB.Tau1408Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb14

open CFSG.KC.Orb14 CertificateChecks.Tau1408

set_option maxRecDepth 100000

theorem eS0 : edgeOK SB NETS ET 0 176 17 693 = true := by quickRfl
theorem eS1 : edgeOK SB NETS ET 176 176 17 693 = true := by quickRfl
theorem eS2 : edgeOK SB NETS ET 352 176 17 693 = true := by quickRfl
theorem eS3 : edgeOK SB NETS ET 528 176 17 693 = true := by quickRfl
theorem eS4 : edgeOK SB NETS ET 704 176 17 693 = true := by quickRfl
theorem eS5 : edgeOK SB NETS ET 880 176 17 693 = true := by quickRfl
theorem eS6 : edgeOK SB NETS ET 1056 176 17 693 = true := by quickRfl
theorem eS7 : edgeOK SB NETS ET 1232 176 17 693 = true := by quickRfl

end CertificateChecks.Orb14

end
