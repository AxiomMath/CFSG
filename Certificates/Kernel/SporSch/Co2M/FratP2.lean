
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

theorem prof2_r0 : rowK (hA (FYZ.getD 16 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 16 []) = true := by
  quickRfl

theorem prof2_r1 : rowK (hA (FYZ.getD 17 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 17 []) = true := by
  quickRfl

theorem prof2_r2 : rowK (hA (FYZ.getD 18 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 18 []) = true := by
  quickRfl

theorem prof2_r3 : rowK (hA (FYZ.getD 19 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 19 []) = true := by
  quickRfl

theorem prof2_r4 : rowK (hA (FYZ.getD 20 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 20 []) = true := by
  quickRfl

theorem prof2_r5 : rowK (hA (FYZ.getD 21 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 21 []) = true := by
  quickRfl

theorem prof2_r6 : rowK (hA (FYZ.getD 22 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 22 []) = true := by
  quickRfl

theorem prof2_r7 : rowK (hA (FYZ.getD 23 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 23 []) = true := by
  quickRfl

theorem prof2 : profAll (FYZ.getD 32 0) (fun w => FYZ.getD w 0) FT0 FT1 profTable 16 8 = true := by
  unfold profAll
  rw [CFSG.KS.Co2P.strictB_eq]
  refine CFSG.KS.Raw.allN_of_forall fun i hi => ?_
  rw [CFSG.KS.Co2P.strictB_eq]
  interval_cases i
  exacts [prof2_r0, prof2_r1, prof2_r2, prof2_r3, prof2_r4, prof2_r5, prof2_r6, prof2_r7]

end CertificateChecks.KernelSporSch.Co2M

end
