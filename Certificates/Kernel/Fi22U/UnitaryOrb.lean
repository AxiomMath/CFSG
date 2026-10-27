module

public import Certificates.Kernel.Sporadic.RawGenOrb
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22U.UOM

meta def SU : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong693 2

meta def BU : Array Nat := #[0, 1, 3, 9, 45]

end CertificateChecks.KernelFi22U.UOM

#ks_raworb CertificateChecks.KernelFi22U.Fi22UO 693 10 64 CertificateChecks.KernelFi22U.UOM.SU
  CertificateChecks.KernelFi22U.UOM.BU 46 CFSG.Monster.B.Fischer.fi22OuterUnitaryDerivations

end
