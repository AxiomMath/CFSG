
module

public import Certificates.Kernel.SporSch.Co1.Stab
public import Certificates.Data.Kernel.SporSch.Co1VOrb
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import Certificates.Kernel.SporSch.Co1.GenVOrb
public meta import Certificates.Kernel.SporSch.Co1.Stab
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Co1.GenVOrb

public section

set_option maxRecDepth 400000

#kss_vorb CertificateChecks.KernelSporSch.Co1Orbs.O0 CertificateChecks.KernelSporSch.Co1Stab.PH0
  CertificateChecks.KernelSporSch.Co1Stab.PH1 16663704 1 1

#kss_vorb CertificateChecks.KernelSporSch.Co1Orbs.O1 CertificateChecks.KernelSporSch.Co1Stab.PH0
  CertificateChecks.KernelSporSch.Co1Stab.PH1 6009710 46575 2048

end
