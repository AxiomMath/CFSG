
module

public import Certificates.Kernel.SporSch.Co2M.FratTr
public import Certificates.Data.Kernel.SporSch.Co2Prof
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.SporSch.Co2ProfSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KS.Co2P CFSG.Sporadic.Co2Schreier

theorem prof3_r0 : rowK (hA (FYZ.getD 24 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 24 []) = true := by
  quickRfl

theorem prof3_r1 : rowK (hA (FYZ.getD 25 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 25 []) = true := by
  quickRfl

theorem prof3_r2 : rowK (hA (FYZ.getD 26 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 26 []) = true := by
  quickRfl

theorem prof3_r3 : rowK (hA (FYZ.getD 27 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 27 []) = true := by
  quickRfl

theorem prof3_r4 : rowK (hA (FYZ.getD 28 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 28 []) = true := by
  quickRfl

theorem prof3_r5 : rowK (hA (FYZ.getD 29 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 29 []) = true := by
  quickRfl

theorem prof3_r6 : rowK (hA (FYZ.getD 30 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 30 []) = true := by
  quickRfl

theorem prof3_r7 : rowK (hA (FYZ.getD 31 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 31 []) = true := by
  quickRfl

theorem prof3 : profAll (FYZ.getD 32 0) (fun w => FYZ.getD w 0) FT0 FT1 profTable 24 8 = true := by
  unfold profAll
  rw [CFSG.KS.Co2P.strictB_eq]
  refine CFSG.KS.Raw.allN_of_forall fun i hi => ?_
  rw [CFSG.KS.Co2P.strictB_eq]
  interval_cases i
  exacts [prof3_r0, prof3_r1, prof3_r2, prof3_r3, prof3_r4, prof3_r5, prof3_r6, prof3_r7]

end CertificateChecks.KernelSporSch.Co2M

end
