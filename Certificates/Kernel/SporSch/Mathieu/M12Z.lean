module

public import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Kernel.SporSch.Mathieu.GenBT
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public meta import Certificates.Kernel.SporSch.Mathieu.M12Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12OC

meta def btHint : String := include_str "M12BT.txt"

end CertificateChecks.KernelSporSch.M12OC

#kss_bt CertificateChecks.KernelSporSch.M12BC CertificateChecks.KernelSporSch.M12Q 12 4 5
  CertificateChecks.KernelSporSch.M12OC.btHint

#kss_classes2 CertificateChecks.KernelSporSch.M12CK 12 4 CertificateChecks.KernelSporSch.M12OC.tAM
  CertificateChecks.KernelSporSch.M12OC.tBM CertificateChecks.KernelSporSch.M12OC.tA
  CertificateChecks.KernelSporSch.M12OC.tB CertificateChecks.KernelSporSch.M12OC.repsM 2 1000

#kss_zscan CertificateChecks.KernelSporSch.M12ZA CertificateChecks.KernelSporSch.M12BC
  CertificateChecks.KernelSporSch.M12CK 12 4 CertificateChecks.KernelSporSch.M12OC.btHint
  CertificateChecks.KernelSporSch.M12OC.tAM
  CertificateChecks.KernelSporSch.M12OC.tBM CertificateChecks.KernelSporSch.M12OC.repsM
  CFSG.Sporadic.Schreier.m12AutWords 2 3 11

end
