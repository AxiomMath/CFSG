module

public import Certificates.Data.Kernel.EvenBN.K3Chain
public import Certificates.Kernel.EvenBN.K28040D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.K28040

open CFSG.KC.K3Chain

theorem ok : chainK [l0, l1, l2] = true := by quickRfl

theorem len : ([l0, l1, l2].map List.length).prod = 25920 := by decide

end CertificateChecks.K28040

end
