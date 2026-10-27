
module

public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.SporSch.Mathieu.M24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M24OC

meta def btHint : String := include_str "M24BT.txt"

end CertificateChecks.KernelSporSch.M24OC

#kss_bt CertificateChecks.KernelSporSch.M24B CertificateChecks.KernelSporSch.M24Q 24 5 7
  CertificateChecks.KernelSporSch.M24OC.btHint

end
