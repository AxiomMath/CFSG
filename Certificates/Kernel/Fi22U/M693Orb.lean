module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22U.MOM

meta def SM : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong693 3

meta def BM : Array Nat := #[0, 1, 3, 9, 45]

end CertificateChecks.KernelFi22U.MOM

#ks_raworb CertificateChecks.KernelFi22U.Fi22MO 693 10 64 CertificateChecks.KernelFi22U.MOM.SM
  CertificateChecks.KernelFi22U.MOM.BM 3 CFSG.Monster.B.Fischer.fi22OuterM693Derivations

end
