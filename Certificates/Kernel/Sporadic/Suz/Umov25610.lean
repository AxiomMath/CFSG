module

public import Certificates.Kernel.Sporadic.Suz.Cent25610Defs
public meta import Certificates.Kernel.Sporadic.Suz.Cent25610Defs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelSpor.SuzUm CertificateChecks.KernelSpor.SuzCI.umovM 11

namespace CertificateChecks.KernelSpor.SuzCI

open CFSG.KC.Enum

theorem umAll : allN 2 (fun i => allN 4 fun j =>
    umovK (SuzUm (Nat.add (Nat.mul 4 i) j)) (SuzTP i) (SuzTP j)) = true := by
  quickRfl

theorem tsAll : tsOK = true := by quickRfl

end CertificateChecks.KernelSpor.SuzCI

end
