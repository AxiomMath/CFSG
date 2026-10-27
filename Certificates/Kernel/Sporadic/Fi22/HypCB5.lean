module

public import Certificates.Kernel.Sporadic.Fi22.HypCB
public meta import Certificates.Kernel.Sporadic.Fi22.HypCB
public import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CB5

meta def lettersM : Array (Array Nat) := Fi22CB.lettersOf 5 [41, 42] [2] 2 [1]

end CertificateChecks.KernelSpor.Fi22CB5

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CB5L CertificateChecks.KernelSpor.Fi22CB5.lettersM 12

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Fi22CB5D
  "Certificates/Kernel/Sporadic/Fi22/data/hypr5.json.gz" 38450 1479281457714663169
  (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Fi22CB5

@[expose] noncomputable def T : Nat := Fi22ExtT.L 26

@[expose] noncomputable def L (z : Nat) : Nat := Fi22CB5L z

theorem lettersAll : Fi22CB.lettersOK L T = true := by quickRfl

theorem baseAll : Fi22CB.baseChk L Fi22CB5D.B Fi22CB5D.PF Fi22CB5D.ZF Fi22CB5D.DF = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CB5

end
