module

public import Certificates.Kernel.Sporadic.Fi22.CentDefs
public meta import Certificates.Kernel.Sporadic.Fi22.CentDefs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CI1

meta def lettersM : Array (Array Nat) := Fi22CI.lettersOf 1 [11, 12]

end CertificateChecks.KernelSpor.Fi22CI1

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CI1L CertificateChecks.KernelSpor.Fi22CI1.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CI1D
  "Certificates/Kernel/Sporadic/Fi22/data/cent1.json.gz" 50973 1900913247620901153
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CI1

@[expose] noncomputable def T : Nat := Fi22ExtT.L 22

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CI1L z

theorem lettersAll : Fi22CI.lettersOK L T = true := by quickRfl

theorem centAll : Fi22CI.centChk L Fi22CI1D.B Fi22CI1D.PF Fi22CI1D.ZF Fi22CI1D.DF
    Fi22CI1D.RF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CI1

end
