module

public import Certificates.Kernel.LyGlue.PtDefs

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition

theorem k_ySec : secOK 66825 1080 FY SY = true := by decide +kernel

theorem k_tSec : secOK 66825 243 FT ST = true := by decide +kernel

theorem k_line : eq22 243 8 (mask 8) (GH.F 0) (LH.F 1) (LH.F 2) (GH.F 0) = true := by
  decide +kernel

theorem k_canon : allN 5 (fun k => Nat.beq (Nat.shiftRight (GH.F k) 1944) 0) = true ∧
    allN 3 (fun k => Nat.beq (Nat.shiftRight (LH.F k) 1944) 0) = true := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem k_img : imgK = true := by decide +kernel

theorem k_txyConj : txyConjK = true := by decide +kernel

theorem k_agree : agreeK = true := by decide +kernel

end CertificateChecks.KernelLy

end
