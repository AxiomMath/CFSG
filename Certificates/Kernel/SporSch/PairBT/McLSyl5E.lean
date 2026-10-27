module

public import Certificates.Kernel.SporSch.PairBT.McLSylEData
public meta import Certificates.Kernel.SporSch.PairBT.McLSylEData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_sylelts CertificateChecks.KernelSporSch.McLS5 CertificateChecks.KernelSporSch.PMcL 275 9 5
  CertificateChecks.KernelSporSch.McLBT.RL5 5 CertificateChecks.KernelSporSch.McLBT.syl5Hint

end
