module

public import Certificates.Kernel.Sporadic.PSp45.Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.Sporadic.PSp45.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PSp45

meta def btHintA : String := include_str "A45BT.txt"

end CertificateChecks.KernelSpor.PSp45

#kss_bt CertificateChecks.KernelSpor.A45B CertificateChecks.KernelSpor.A45Q 45 6 4
  CertificateChecks.KernelSpor.PSp45.btHintA

end
