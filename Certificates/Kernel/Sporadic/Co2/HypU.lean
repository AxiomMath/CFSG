module

public import Certificates.Kernel.Sporadic.Co2.HypDefs
public import Certificates.Kernel.SporSch.Co2M.ChainS
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Co2.ChainA

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co2HU
  "Certificates/Kernel/Sporadic/Co2/data/hypu.json.gz" 91959 4419836504102010645
  (LS : List Nat) (B : List CFSG.KC.CommBase.BaseRec) (PF : Nat) (ZF : Nat) (DF : Nat)

namespace CertificateChecks.KernelSpor.Co2HU

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.CommBase

@[expose] noncomputable def R : Nat := Co2H.c (KernelSporSch.Co2LS.S 8) (KernelSporSch.Co2LS.S 0)

@[expose] noncomputable def L (k : Nat) : Nat := Co2H.letL LS R 4 k

theorem lettersAll : Co2H.letOK L R 4 = true := by quickRfl

theorem baseAll : commBaseOK 2300 12 (mask 12) L 9 B PF ZF DF = true := by quickRfl

end CertificateChecks.KernelSpor.Co2HU

end
