module

public import Certificates.Kernel.Sporadic.Fi22.CentDefs
public meta import Certificates.Kernel.Sporadic.Fi22.CentDefs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CI4

meta def lettersM : Array (Array Nat) := Fi22CI.lettersOf 4 [33, 34]

end CertificateChecks.KernelSpor.Fi22CI4

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CI4L CertificateChecks.KernelSpor.Fi22CI4.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CI4D
  "Certificates/Kernel/Sporadic/Fi22/data/cent4.json.gz" 50834 16416027005556091494
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CI4

@[expose] noncomputable def T : Nat := Fi22ExtT.L 25

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CI4L z

theorem lettersAll : Fi22CI.lettersOK L T = true := by quickRfl

theorem centAll : Fi22CI.centChk L Fi22CI4D.B Fi22CI4D.PF Fi22CI4D.ZF Fi22CI4D.DF
    Fi22CI4D.RF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CI4

end
