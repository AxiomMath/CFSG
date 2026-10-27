module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CB3

meta def lettersM : Array (Array Nat) := Fi22CB.lettersOf 3 [26, 27] [1, -2, -2] 2 [2]

end CertificateChecks.KernelSpor.Fi22CB3

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CB3L CertificateChecks.KernelSpor.Fi22CB3.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CB3D
  "Certificates/Kernel/Sporadic/Fi22/data/hypr3.json.gz" 38284 16324388889531258501
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CB3

@[expose] noncomputable def T : Nat := Fi22ExtT.L 24

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CB3L z

theorem lettersAll : Fi22CB.lettersOK L T = true := by quickRfl

theorem baseAll : Fi22CB.baseChk L Fi22CB3D.B Fi22CB3D.PF Fi22CB3D.ZF Fi22CB3D.DF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CB3

end
