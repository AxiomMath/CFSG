module

public import Certificates.Kernel.SporSch.HN.T0Data
public import Certificates.Data.Kernel.SporSch.HNT0
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSporSch.HNT0

open CFSG.KD.HNT0 CFSG.KS.HNT0 CFSG.KS.EnumBase

#kc_each CertificateChecks.KernelSporSch.HNT0 ch10509c
  (fun s => sliceK 16384 64 (clK 192 8 255 4 16384 G T POS) s) 128 192

end CertificateChecks.KernelSporSch.HNT0

end
