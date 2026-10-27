module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Sporadic.FischerOddCore.Fi22CentText
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22CP0 CFSG.Sporadic.FischerOddCore.fi22CentP0
#ks_chars CertificateChecks.KernelSpor.Fi22CP1 CFSG.Sporadic.FischerOddCore.fi22CentP1
#ks_chars CertificateChecks.KernelSpor.Fi22CP2 CFSG.Sporadic.FischerOddCore.fi22CentP2
#ks_chars CertificateChecks.KernelSpor.Fi22CP3 CFSG.Sporadic.FischerOddCore.fi22CentP3

end
