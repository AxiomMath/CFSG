module

public import Certificates.Kernel.Y63.Data

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem q2 : dK.QSpec 2 := by decide +kernel

theorem q3 : dK.QSpec 3 := by decide +kernel

end CertificateChecks.KernelY63

end
