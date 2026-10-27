module

public import Certificates.Kernel.MonsterB.Orb3132Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb3132

set_option maxRecDepth 100000

theorem s35_11 : slice 35 rec35 798336 4 20 330 30 = true := by quickRfl

theorem s35_12 : slice 35 rec35 798336 4 20 360 30 = true := by quickRfl

end CertificateChecks.Orb3132

end
