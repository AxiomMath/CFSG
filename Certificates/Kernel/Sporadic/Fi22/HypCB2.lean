module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CB2

meta def lettersM : Array (Array Nat) := Fi22CB.lettersOf 2 [19, 20] [2] 2 [1]

end CertificateChecks.KernelSpor.Fi22CB2

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CB2L CertificateChecks.KernelSpor.Fi22CB2.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CB2D
  "Certificates/Kernel/Sporadic/Fi22/data/hypr2.json.gz" 38217 12514197126821177737
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CB2

@[expose] noncomputable def T : Nat := Fi22ExtT.L 23

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CB2L z

theorem lettersAll : Fi22CB.lettersOK L T = true := by quickRfl

theorem baseAll : Fi22CB.baseChk L Fi22CB2D.B Fi22CB2D.PF Fi22CB2D.ZF Fi22CB2D.DF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CB2

end
