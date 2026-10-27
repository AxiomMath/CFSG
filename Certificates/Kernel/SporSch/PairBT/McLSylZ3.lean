module

public import Certificates.Kernel.SporSch.PairBT.McLSylData
public import Certificates.Kernel.SporSch.PairBT.McLCls
public import Certificates.Kernel.SporSch.PairBT.McLWData
public meta import Certificates.Kernel.SporSch.PairBT.McLSylData
public meta import Certificates.Kernel.SporSch.PairBT.McLData
public meta import Certificates.Kernel.SporSch.PairBT.McLWData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_zscan CertificateChecks.KernelSporSch.McLSylZ3 CertificateChecks.KernelSporSch.McLSyl
  CertificateChecks.KernelSporSch.McLCK 275 9 CertificateChecks.KernelSporSch.McLBT.sylHint
  CertificateChecks.KernelSporSch.McLBT.tAM CertificateChecks.KernelSporSch.McLBT.tBM
  CertificateChecks.KernelSporSch.McLBT.repsM CertificateChecks.KernelSporSch.McLBT.ws3 2 5 11

end
