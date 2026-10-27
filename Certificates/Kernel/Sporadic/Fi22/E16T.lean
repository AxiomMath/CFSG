module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22E16Inputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22E16Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22E16T CFSG.EvenSporadicStandard.YS14.fi22E16Text

#ks_hexlines CertificateChecks.KernelSpor.Fi22E16T CFSG.EvenSporadicStandard.YS14.fi22E16Text 3 3510 12

end
