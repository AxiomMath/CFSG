module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22OC

meta def btHint : String := include_str "M22BT.txt"

end CertificateChecks.KernelSporSch.M22OC

#kss_bt CertificateChecks.KernelSporSch.M22B CertificateChecks.KernelSporSch.M22Q 22 5 5
  CertificateChecks.KernelSporSch.M22OC.btHint

end
