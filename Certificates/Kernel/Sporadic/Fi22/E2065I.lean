module

public import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.Misc.Perm.HexCmd

public section

namespace CertificateChecks.KernelSpor.Fi22E2065

meta def invM : Array (Array Nat) := (Array.range 306).map fun L =>
  CFSG.Monster.B.Co2.Native.invCand 3510 (CFSG.Sporadic.FischerOddCore.fi22CentArr L)

end CertificateChecks.KernelSpor.Fi22E2065

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22E2065.CI CertificateChecks.KernelSpor.Fi22E2065.invM 12

end
