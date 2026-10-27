module

public import Certificates.Kernel.Sporadic.Fi22.CentDefs
public meta import Certificates.Kernel.Sporadic.Fi22.CentDefs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CI0

meta def lettersM : Array (Array Nat) := Fi22CI.lettersOf 0 [4, 5]

end CertificateChecks.KernelSpor.Fi22CI0

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CI0L CertificateChecks.KernelSpor.Fi22CI0.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CI0D
  "Certificates/Kernel/Sporadic/Fi22/data/cent0.json.gz" 51096 521648362260754846
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CI0

@[expose] noncomputable def T : Nat := Fi22ExtT.L 21

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CI0L z

theorem lettersAll : Fi22CI.lettersOK L T = true := by quickRfl

theorem centAll : Fi22CI.centChk L Fi22CI0D.B Fi22CI0D.PF Fi22CI0D.ZF Fi22CI0D.DF
    Fi22CI0D.RF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CI0

end
