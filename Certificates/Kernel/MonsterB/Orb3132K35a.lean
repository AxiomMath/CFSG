module

public import Certificates.Kernel.MonsterB.Orb3132Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb3132

set_option maxRecDepth 100000

theorem s35_0 : slice 35 rec35 798336 4 20 0 30 = true := by quickRfl

theorem s35_1 : slice 35 rec35 798336 4 20 30 30 = true := by quickRfl

theorem s35_2 : slice 35 rec35 798336 4 20 60 30 = true := by quickRfl

end CertificateChecks.Orb3132

end
