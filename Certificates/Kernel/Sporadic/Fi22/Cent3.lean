module

public import Certificates.Kernel.Sporadic.Fi22.CentDefs
public meta import Certificates.Kernel.Sporadic.Fi22.CentDefs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CI3

meta def lettersM : Array (Array Nat) := Fi22CI.lettersOf 3 [26, 27]

end CertificateChecks.KernelSpor.Fi22CI3

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CI3L CertificateChecks.KernelSpor.Fi22CI3.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CI3D
  "Certificates/Kernel/Sporadic/Fi22/data/cent3.json.gz" 50968 8949417103238400748
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CI3

@[expose] noncomputable def T : Nat := Fi22ExtT.L 24

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CI3L z

theorem lettersAll : Fi22CI.lettersOK L T = true := by quickRfl

theorem centAll : Fi22CI.centChk L Fi22CI3D.B Fi22CI3D.PF Fi22CI3D.ZF Fi22CI3D.DF
    Fi22CI3D.RF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CI3

end
