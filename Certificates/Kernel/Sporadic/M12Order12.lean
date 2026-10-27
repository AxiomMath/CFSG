module

public import Certificates.Kernel.Sporadic.M12Count
public import Certificates.Data.Kernel.Spor.PCount12
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M12Count

open CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt

set_option maxRecDepth 100000

@[expose] noncomputable def cnt12S (j : Nat) : Nat :=
  pcnt 12 4 (mask 4) (ordTwelve 12 4 (mask 4) I) ((slice j).map fun T => T.map pk) I 0

theorem o12s0 : Nat.beq (cnt12S 0) 0 = true := by quickRfl

theorem o12s1 : Nat.beq (cnt12S 1) 0 = true := by quickRfl

theorem o12s2 : Nat.beq (cnt12S 2) 0 = true := by quickRfl

theorem o12s3 : Nat.beq (cnt12S 3) 0 = true := by quickRfl

end CertificateChecks.KernelSpor.M12Count

end
