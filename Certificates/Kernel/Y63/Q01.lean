module

public import Certificates.Kernel.Y63.Data

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem q0 : dK.QSpec 0 := by decide +kernel

theorem q1 : dK.QSpec 1 := by decide +kernel

end CertificateChecks.KernelY63

end
