module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.Bases
public meta import Certificates.Kernel.OmegaEight.Bases
public import Certificates.Kernel.OmegaEight.Bases3009
public meta import Certificates.Kernel.OmegaEight.Bases3009
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelO8.AQ 360 9 24 CFSG.EvenSmallLie.OmegaEight.autS
  CertificateChecks.KernelO8.omBaseP 10 CFSG.EvenSmallLie.OmegaEight.autWords

#ks_rawchain CertificateChecks.KernelO8.SY 360 9 24 CFSG.EvenSmallLie.OmegaEight.sylowS
  CertificateChecks.KernelO8.syBaseP 5 CFSG.EvenSmallLie.OmegaEight.sylowWords

end
