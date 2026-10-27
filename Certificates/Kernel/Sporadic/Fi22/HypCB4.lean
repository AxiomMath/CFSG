module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CB4

meta def lettersM : Array (Array Nat) := Fi22CB.lettersOf 4 [33, 34] [1, -2] 4 [1]

end CertificateChecks.KernelSpor.Fi22CB4

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CB4L CertificateChecks.KernelSpor.Fi22CB4.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CB4D
  "Certificates/Kernel/Sporadic/Fi22/data/hypr4.json.gz" 38261 3006960689037667504
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CB4

@[expose] noncomputable def T : Nat := Fi22ExtT.L 25

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CB4L z

theorem lettersAll : Fi22CB.lettersOK L T = true := by quickRfl

theorem baseAll : Fi22CB.baseChk L Fi22CB4D.B Fi22CB4D.PF Fi22CB4D.ZF Fi22CB4D.DF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CB4

end
