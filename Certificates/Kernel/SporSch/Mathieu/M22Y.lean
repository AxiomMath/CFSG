module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.Gen2F
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_cntword2f CertificateChecks.KernelSporSch.M22Y0 CertificateChecks.KernelSporSch.M22Q 22 5
  CertificateChecks.KernelSporSch.M22OC.SM CertificateChecks.KernelSporSch.M22OC.baseM 2 4
  CFSG.Sporadic.Schreier.m22AutWords CertificateChecks.KernelSporSch.M22OC.R0
  CertificateChecks.KernelSporSch.M22OC.rep0M

end
