module

public import Certificates.Kernel.Sporadic.RawTreeSplit
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawtree_data CertificateChecks.KernelSpor.Fi22R6 3510 12 64 64
  CFSG.Monster.B.Fischer.fi22StrongArrs CFSG.Monster.B.Fischer.fi22BaseArr 2
  CFSG.Monster.B.Fischer.fi22ChainDerivations

end
