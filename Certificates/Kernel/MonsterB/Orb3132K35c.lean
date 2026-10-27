module

public import Certificates.Kernel.MonsterB.Orb3132Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb3132

set_option maxRecDepth 100000

theorem s35_6 : slice 35 rec35 798336 4 20 180 30 = true := by quickRfl

theorem s35_7 : slice 35 rec35 798336 4 20 210 30 = true := by quickRfl

theorem s35_8 : slice 35 rec35 798336 4 20 240 30 = true := by quickRfl

end CertificateChecks.Orb3132

end
