module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.Bases
public meta import Certificates.Kernel.OmegaEight.Bases
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.W3185.Om1 120 9 12 CFSG.EvenSmallLie.OmegaEight.omega1S
  CertificateChecks.KernelO8.omBaseP 8 CFSG.EvenSmallLie.OmegaEight.omegaWords

end
