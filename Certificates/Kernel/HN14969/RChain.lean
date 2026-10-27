module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.HN14969.Data
meta import Certificates.Kernel.HN14969.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelHN14969.RC 126 7 16 CertificateChecks.KernelHN14969.rS
  CertificateChecks.KernelHN14969.rBase 2 CertificateChecks.KernelHN14969.dR
