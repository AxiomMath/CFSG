module

public import Certificates.Kernel.Sporadic.Co2.HypZ
public import Certificates.Kernel.Sporadic.Co2.HypT
public import Certificates.Kernel.Sporadic.Co2.HypU
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co2SQ
  "Certificates/Kernel/Sporadic/Co2/data/sq24960.json.gz" 49899 11705142753478609362
  (W0 : Nat) (I0 : Nat) (W1 : Nat) (I1 : Nat) (W2 : Nat) (I2 : Nat)

namespace CertificateChecks.KernelSpor.Co2SQ

@[expose] noncomputable def sqK (W I R : Nat) : Bool :=
  Co2H.perm W I && Co2H.siftP W && Nat.beq (Co2H.c W W) R

theorem sqZ : sqK W0 I0 Co2HZ.R = true := by quickRfl

theorem sqT : sqK W1 I1 Co2HT.R = true := by quickRfl

theorem sqU : sqK W2 I2 Co2HU.R = true := by quickRfl

theorem sqNeg : (!sqK W0 I0 Co2HT.R) = true ∧ (!sqK W0 I1 Co2HZ.R) = true :=
  ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelSpor.Co2SQ

end
