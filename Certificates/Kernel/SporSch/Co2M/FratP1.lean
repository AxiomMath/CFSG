
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

theorem prof1_r0 : rowK (hA (FYZ.getD 8 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 8 []) = true := by
  quickRfl

theorem prof1_r1 : rowK (hA (FYZ.getD 9 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 9 []) = true := by
  quickRfl

theorem prof1_r2 : rowK (hA (FYZ.getD 10 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 10 []) = true := by
  quickRfl

theorem prof1_r3 : rowK (hA (FYZ.getD 11 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 11 []) = true := by
  quickRfl

theorem prof1_r4 : rowK (hA (FYZ.getD 12 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 12 []) = true := by
  quickRfl

theorem prof1_r5 : rowK (hA (FYZ.getD 13 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 13 []) = true := by
  quickRfl

theorem prof1_r6 : rowK (hA (FYZ.getD 14 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 14 []) = true := by
  quickRfl

theorem prof1_r7 : rowK (hA (FYZ.getD 15 0) (Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)) FT1 FT0 0)
    (profTable.getD 15 []) = true := by
  quickRfl

theorem prof1 : profAll (FYZ.getD 32 0) (fun w => FYZ.getD w 0) FT0 FT1 profTable 8 8 = true := by
  unfold profAll
  rw [CFSG.KS.Co2P.strictB_eq]
  refine CFSG.KS.Raw.allN_of_forall fun i hi => ?_
  rw [CFSG.KS.Co2P.strictB_eq]
  interval_cases i
  exacts [prof1_r0, prof1_r1, prof1_r2, prof1_r3, prof1_r4, prof1_r5, prof1_r6, prof1_r7]

end CertificateChecks.KernelSporSch.Co2M

end
