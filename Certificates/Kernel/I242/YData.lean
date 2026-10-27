module

public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.I242.Base
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Inputs
public meta import Certificates.Kernel.I242.Base
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelI242.Y 3510 12 2 64
  CFSG.HardMathSupport.Solomon.Coordinator.i242S CertificateChecks.KernelI242.i242BaseA 8
  CFSG.EvenSmallLie.OmegaEight.omegaWords

end
