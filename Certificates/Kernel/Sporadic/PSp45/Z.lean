module

public import Certificates.Kernel.Sporadic.PSp45.Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.Sporadic.PSp45.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PSp45

meta def btHint : String := include_str "P45BT.txt"

end CertificateChecks.KernelSpor.PSp45

#kss_bt CertificateChecks.KernelSpor.P45BC CertificateChecks.KernelSpor.P45Q 45 6 4
  CertificateChecks.KernelSpor.PSp45.btHint

#kss_classes2 CertificateChecks.KernelSpor.P45CK 45 6 CertificateChecks.KernelSpor.PSp45.tXM
  CertificateChecks.KernelSpor.PSp45.tYM CertificateChecks.KernelSpor.PSp45.tX
  CertificateChecks.KernelSpor.PSp45.tY CertificateChecks.KernelSpor.PSp45.repsM 2 1000

#kss_zscan CertificateChecks.KernelSpor.P45ZA CertificateChecks.KernelSpor.P45BC
  CertificateChecks.KernelSpor.P45CK 45 6 CertificateChecks.KernelSpor.PSp45.btHint
  CertificateChecks.KernelSpor.PSp45.tXM
  CertificateChecks.KernelSpor.PSp45.tYM CertificateChecks.KernelSpor.PSp45.repsM
  CertificateChecks.KernelSpor.PSp45.ws45N 2 5 9

end
