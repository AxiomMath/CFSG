module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.HN14969.Data
meta import Certificates.Kernel.HN14969.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelHN14969.HC 176 8 16 CertificateChecks.KernelHN14969.hS
  CertificateChecks.KernelHN14969.hBase 2 CertificateChecks.KernelHN14969.dH
