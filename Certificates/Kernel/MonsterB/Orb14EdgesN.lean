module

public import Certificates.Data.Kernel.MonsterB.Orb14
public import Certificates.Kernel.MonsterB.Orb14Net
public import Certificates.Kernel.MonsterB.Tau1408Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb14

open CFSG.KC.Orb14 CertificateChecks.Tau1408

set_option maxRecDepth 100000

theorem eN0 : edgeOK SBN NETN ET 0 176 17 891 = true := by quickRfl
theorem eN1 : edgeOK SBN NETN ET 176 176 17 891 = true := by quickRfl
theorem eN2 : edgeOK SBN NETN ET 352 176 17 891 = true := by quickRfl
theorem eN3 : edgeOK SBN NETN ET 528 176 17 891 = true := by quickRfl
theorem eN4 : edgeOK SBN NETN ET 704 176 17 891 = true := by quickRfl
theorem eN5 : edgeOK SBN NETN ET 880 176 17 891 = true := by quickRfl
theorem eN6 : edgeOK SBN NETN ET 1056 176 17 891 = true := by quickRfl
theorem eN7 : edgeOK SBN NETN ET 1232 176 17 891 = true := by quickRfl

end CertificateChecks.Orb14

end
