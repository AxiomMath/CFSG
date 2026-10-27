module

public import Certificates.Kernel.Sporadic.Fi22.CentDefs
public meta import Certificates.Kernel.Sporadic.Fi22.CentDefs
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CI2

meta def lettersM : Array (Array Nat) := Fi22CI.lettersOf 2 [19, 20]

end CertificateChecks.KernelSpor.Fi22CI2

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CI2L CertificateChecks.KernelSpor.Fi22CI2.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CI2D
  "Certificates/Kernel/Sporadic/Fi22/data/cent2.json.gz" 50893 8285807650289056912
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat) (RF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CI2

@[expose] noncomputable def T : Nat := Fi22ExtT.L 23

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CI2L z

theorem lettersAll : Fi22CI.lettersOK L T = true := by quickRfl

theorem centAll : Fi22CI.centChk L Fi22CI2D.B Fi22CI2D.PF Fi22CI2D.ZF Fi22CI2D.DF
    Fi22CI2D.RF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CI2

end
