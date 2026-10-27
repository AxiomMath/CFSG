
module

public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23OC

meta def btHint : String := include_str "M23BT.txt"

end CertificateChecks.KernelSporSch.M23OC

#kss_bt CertificateChecks.KernelSporSch.M23B CertificateChecks.KernelSporSch.M23Q 23 5 6
  CertificateChecks.KernelSporSch.M23OC.btHint

end
