module

public import Certificates.Kernel.Sporadic.Suz.Cent25610Defs
public meta import Certificates.Kernel.Sporadic.Suz.Cent25610Defs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCI0

meta def lettersM : Array (Array Nat) := SuzCI.lettersOf 0 [4, 5]

end CertificateChecks.KernelSpor.SuzCI0

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCI0L CertificateChecks.KernelSpor.SuzCI0.lettersM 11

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzCI0D
  "Certificates/Kernel/Sporadic/Suz/data/cent25610_0.json.gz" 23805 12375504321853266809
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.SuzCI0

@[expose] noncomputable def L (z : Nat) : Nat := SuzCI0L z

theorem lettersAll : SuzCI.lettersOK L (SuzTP 0) = true := by quickRfl

theorem centAll : SuzCI.centChk L SuzCI0D.B SuzCI0D.PF SuzCI0D.ZF SuzCI0D.DF SuzCI0D.RF =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.SuzCI0

end
