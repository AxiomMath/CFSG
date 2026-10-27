module

public import Certificates.Kernel.LyS0.Data
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.LyS0.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyS0

open CFSG.KD.LyS0

theorem gensC : gensK CertificateChecks.KernelSporSch.LyBS.A CertificateChecks.KernelSporSch.LyBS.B
    T GI = true := by quickRfl

end CertificateChecks.KernelLyS0

end
