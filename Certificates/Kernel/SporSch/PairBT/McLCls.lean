module

public import Certificates.Kernel.SporSch.PairBT.McLData
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.SporSch.PairBT.McLData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CertificateChecks.KernelSporSch.McLCK 275 9 CertificateChecks.KernelSporSch.McLBT.tAM
  CertificateChecks.KernelSporSch.McLBT.tBM CertificateChecks.KernelSporSch.McLBT.tA
  CertificateChecks.KernelSporSch.McLBT.tB CertificateChecks.KernelSporSch.McLBT.repsM 2 30000

end
