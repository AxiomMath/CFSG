module

public import Certificates.Kernel.MonsterB.Orb3132Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb3132

set_option maxRecDepth 100000

theorem s60 : slice 60 rec60 1408 3 11 0 1 = true := by quickRfl

theorem s32 : slice 32 rec32 20736 4 15 0 11 = true := by quickRfl

end CertificateChecks.Orb3132

end
