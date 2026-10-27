module

public import Certificates.Kernel.MonsterB.Orb3132Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb3132

set_option maxRecDepth 100000

theorem s39_2 : slice 39 rec39 228096 4 18 56 28 = true := by quickRfl

theorem s39_3 : slice 39 rec39 228096 4 18 84 28 = true := by quickRfl

end CertificateChecks.Orb3132

end
