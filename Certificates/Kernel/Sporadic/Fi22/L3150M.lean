
module

public import Certificates.Kernel.Sporadic.Fi22.Ext2073
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheckBase
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22M3

meta def outM3M : Array (Array Nat) := CFSG.Monster.B.Fischer.fi22OuterStrong3510 3

end CertificateChecks.KernelSpor.Fi22M3

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22M3.MS CertificateChecks.KernelSpor.Fi22M3.outM3M 12

namespace CertificateChecks.KernelSpor.Fi22M3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CertificateChecks.KernelSpor

@[expose] noncomputable def lineOK (j : Nat) : Bool :=
  lineK 3 3510 12 (MS j) (Fi22OutT.chars.drop (Nat.mul (Nat.add (nat_lit 3) j) (nat_lit 10531)))

end CertificateChecks.KernelSpor.Fi22M3

#kon_slices CertificateChecks.KernelSpor.Fi22M3.lineOK 0 17

#kon_join CertificateChecks.KernelSpor.Fi22M3.all CertificateChecks.KernelSpor.Fi22M3.lineOK 17

end
