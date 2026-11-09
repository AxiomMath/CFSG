module

public import Certificates.Kernel.SporSch.Mathieu.M12MData
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public meta import Certificates.Kernel.SporSch.Mathieu.M12MData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12MOC

meta def btHint : String := include_str "M12DBT.txt"

end CertificateChecks.KernelSporSch.M12MOC

#kss_bt CertificateChecks.KernelSporSch.M12DB CertificateChecks.KernelSporSch.M12DQ 24 5 5
  CertificateChecks.KernelSporSch.M12MOC.btHint

end
