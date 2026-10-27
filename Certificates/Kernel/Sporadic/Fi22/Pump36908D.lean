module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Fi22Pump
public meta import Certificates.Data.Fi22Pump
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

set_option Elab.async false

#ks_chars CertificateChecks.KernelSpor.Fi22PumpT
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.pumpHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22PumpT
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.pumpHex 3 3510 12 3
