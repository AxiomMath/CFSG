module

public import Certificates.Data.Kernel.L34Q.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 100000

#kc_repo #kc_json_gz CFSG.KD.L34Q "Certificates/Kernel/L34Q/l34q.json.gz" 39181 6712423935691415463
  (D : List (Nat × (Nat × Nat))) (R : List Nat) (R2 : List Nat)

public section

namespace CFSG.KD.L34Q

open CFSG.KC.L34Q

theorem ch7212inv : eqRecs invRecsK D = true := by decide +kernel

theorem ch7212cap : capOKK D R = true := by decide +kernel

theorem ch7212plus : plusOKK D R2 = true := by decide +kernel

theorem ch7212inv_neg : eqRecs invRecsK (List.drop 1 D) = false := by decide +kernel

theorem ch7212cap_neg : capOKK D (List.drop 1 R) = false := by decide +kernel

theorem ch7212plus_neg : plusOKK D (List.drop 1 R2) = false := by decide +kernel

end CFSG.KD.L34Q
