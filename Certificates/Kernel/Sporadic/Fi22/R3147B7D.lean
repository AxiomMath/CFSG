module

public import Certificates.Kernel.Sporadic.RawTreeSplit
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22R

meta def B7M : Array Nat := #[0, 1, 2, 3, 6, 4, 10]

end CertificateChecks.KernelSpor.Fi22R

#ks_rawtree_data CertificateChecks.KernelSpor.Fi22R7 3510 12 64 64
  CFSG.Monster.B.Fischer.fi22StrongArrs CertificateChecks.KernelSpor.Fi22R.B7M 2
  CFSG.Monster.B.Fischer.fi22ChainDerivations

end
