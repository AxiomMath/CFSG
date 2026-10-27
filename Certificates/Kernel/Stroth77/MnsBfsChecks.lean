module

public import Certificates.Kernel.Stroth77.MnsData
public import Certificates.Data.Kernel.Stroth77.MnsBfsK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMnsB778702

open CFSG.KC.Stroth77MN CertificateChecks.KernelMns778702

theorem ch778702b_bfs : bfsOK tabs = true := by quickRfl

end CertificateChecks.KernelMnsB778702
