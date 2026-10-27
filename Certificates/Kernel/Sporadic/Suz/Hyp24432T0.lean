module

public import Certificates.Kernel.Sporadic.Suz.Hyp24432Defs
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Spor.CommEnum

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.SuzH0
  "Certificates/Kernel/Sporadic/Suz/data/hyp24432_hyp0.json.gz" 153904 18010441802755832068
  (LS : List Nat) (R : List CFSG.KC.CommEnum.RepRec) (O : Nat) (PF : Nat) (ZF : Nat) (DF : Nat)
  (Y : List Nat) (YI : List Nat)

namespace CertificateChecks.KernelSpor.SuzH0

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase CFSG.KC.CommEnum

@[expose] noncomputable def L (k : Nat) : Nat := SuzH.letL LS (SuzTP 0) 3 k

@[expose] noncomputable def Yk (k : Nat) : Nat := Y.getD k 0

@[expose] noncomputable def YIk (k : Nat) : Nat := YI.getD k 0

theorem lettersAll : SuzH.letOK L (SuzTP 0) 3 = true := by quickRfl

theorem yAll : SuzH.yOK Yk YIk L 3 8 = true := by quickRfl

theorem enumAll : enumOK 1782 11 (mask 11) L 7 R O PF ZF DF Yk 8 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzH0

end
