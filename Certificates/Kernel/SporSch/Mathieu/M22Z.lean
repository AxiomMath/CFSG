module

public import Certificates.Kernel.SporSch.Mathieu.M22BT
public import Certificates.Kernel.SporSch.Mathieu.M22Cls
public meta import Certificates.Kernel.SporSch.Mathieu.M22BT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_zscan CertificateChecks.KernelSporSch.M22ZA CertificateChecks.KernelSporSch.M22B
  CertificateChecks.KernelSporSch.M22CK 22 5 CertificateChecks.KernelSporSch.M22OC.btHint
  CertificateChecks.KernelSporSch.M22OC.tAM
  CertificateChecks.KernelSporSch.M22OC.tBM CertificateChecks.KernelSporSch.M22OC.repsM
  CFSG.Sporadic.Schreier.m22AutWords 2 4 11

end
