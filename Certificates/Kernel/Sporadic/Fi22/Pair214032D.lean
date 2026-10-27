module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Fi22PairSize
public meta import Certificates.Data.Fi22PairSize
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

set_option Elab.async false

#ks_chars CertificateChecks.KernelSpor.Fi22PairT
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.pairHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22PairT
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump.pairHex 3 3510 12 2
