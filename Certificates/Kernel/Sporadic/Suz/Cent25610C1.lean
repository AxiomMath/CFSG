module

public import Certificates.Kernel.Sporadic.Suz.Cent25610Defs
public meta import Certificates.Kernel.Sporadic.Suz.Cent25610Defs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCI1

meta def lettersM : Array (Array Nat) := SuzCI.lettersOf 1 [10, 11]

end CertificateChecks.KernelSpor.SuzCI1

#kmisc_packarrs CertificateChecks.KernelSpor.SuzCI1L CertificateChecks.KernelSpor.SuzCI1.lettersM 11

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzCI1D
  "Certificates/Kernel/Sporadic/Suz/data/cent25610_1.json.gz" 23750 5039512780752680603
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.SuzCI1

@[expose] noncomputable def L (z : Nat) : Nat := SuzCI1L z

theorem lettersAll : SuzCI.lettersOK L (SuzTP 1) = true := by quickRfl

theorem centAll : SuzCI.centChk L SuzCI1D.B SuzCI1D.PF SuzCI1D.ZF SuzCI1D.DF SuzCI1D.RF =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.SuzCI1

end
