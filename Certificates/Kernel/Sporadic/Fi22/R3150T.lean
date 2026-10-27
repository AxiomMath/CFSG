module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22TRM

meta def ST : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong3510 4

meta def BT : Array Nat := #[0, 1, 2, 3, 6, 4]

end CertificateChecks.KernelSpor.Fi22TRM

#ks_rawtree CertificateChecks.KernelSpor.Fi22TR 3510 12 64 64 0
  CertificateChecks.KernelSpor.Fi22TRM.ST CertificateChecks.KernelSpor.Fi22TRM.BT 9
  CFSG.Monster.B.Fischer.fi22OuterTDerivations

end
