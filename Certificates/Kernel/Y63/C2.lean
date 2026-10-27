module

public import Certificates.Kernel.Y63.Data

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelY63

open CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

theorem mul : dK.MulSpec := by decide +kernel

end CertificateChecks.KernelY63

end
