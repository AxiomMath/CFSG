module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.SporSch.HNT0P
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0 CFSG.KS.EnumBase

#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509a
  (fun s => sliceK 687 8 (adjK 687 8 255 BP 24 IL AL PR KB) s) 43 86

end CertificateChecks.KernelSporSch.HNT0

end
