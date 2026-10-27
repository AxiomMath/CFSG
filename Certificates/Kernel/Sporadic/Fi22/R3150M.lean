module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22MRM

meta def SM : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong3510 3

meta def BM : Array Nat := #[0, 1, 2, 6, 4, 3]

end CertificateChecks.KernelSpor.Fi22MRM

#ks_rawtree CertificateChecks.KernelSpor.Fi22MR 3510 12 64 64 0
  CertificateChecks.KernelSpor.Fi22MRM.SM CertificateChecks.KernelSpor.Fi22MRM.BM 3
  CFSG.Monster.B.Fischer.fi22OuterMDerivations

end
