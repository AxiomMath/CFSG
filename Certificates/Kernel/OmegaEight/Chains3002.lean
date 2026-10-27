module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.Bases3002
public meta import Certificates.Kernel.OmegaEight.Bases3002
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelO8.OmM 136 8 17 CFSG.EvenSmallLie.OmegaEightMinus.omegaS
  CertificateChecks.KernelO8.omBaseM 10 CFSG.EvenSmallLie.OmegaEightMinus.omegaWords

#ks_rawchain CertificateChecks.KernelO8.AQM 136 8 17 CFSG.EvenSmallLie.OmegaEightMinus.autS
  CertificateChecks.KernelO8.autBaseM 11 CFSG.EvenSmallLie.OmegaEightMinus.autWords

#ks_rawchain CertificateChecks.KernelO8.SYM 136 8 17 CFSG.EvenSmallLie.OmegaEightMinus.sylowS
  CertificateChecks.KernelO8.syBaseM 6 CFSG.EvenSmallLie.OmegaEightMinus.sylowWords

end
