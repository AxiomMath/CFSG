module

public import Certificates.Kernel.Sporadic.PSp45.P45BT
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.Sporadic.PSp45.P45BT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_classes2 CertificateChecks.KernelSpor.P45CK 45 6 CertificateChecks.KernelSpor.PSp45.tXM
  CertificateChecks.KernelSpor.PSp45.tYM CertificateChecks.KernelSpor.PSp45.tX
  CertificateChecks.KernelSpor.PSp45.tY CertificateChecks.KernelSpor.PSp45.repsM 2 1000

#kss_zscan CertificateChecks.KernelSpor.P45Z CertificateChecks.KernelSpor.P45B
  CertificateChecks.KernelSpor.P45CK 45 6 CertificateChecks.KernelSpor.PSp45.btHintP
  CertificateChecks.KernelSpor.PSp45.tXM
  CertificateChecks.KernelSpor.PSp45.tYM CertificateChecks.KernelSpor.PSp45.repsM
  CertificateChecks.KernelSpor.PSp45.ws45N 2 5 9

end
