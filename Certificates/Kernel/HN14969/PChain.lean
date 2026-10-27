module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.HN14969.Data
meta import Certificates.Kernel.HN14969.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelHN14969.PC 50 6 10 CertificateChecks.KernelHN14969.pS
  CertificateChecks.KernelHN14969.pBase 2 CertificateChecks.KernelHN14969.dP
