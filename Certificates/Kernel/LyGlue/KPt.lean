module

public import Certificates.Kernel.LyGlue.PtDefs

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition

theorem k_c2 : allN 66825 (fun a => Nat.beq (cL (cL a)) a) = true := by decide +kernel

theorem k_d3 : allN 66825 (fun a => Nat.beq (dL (dL (dL a))) a) = true := by decide +kernel

theorem k_ySec : secOK 66825 1080 FY SY = true := by decide +kernel

theorem k_tSec : secOK 66825 243 FT ST = true := by decide +kernel

theorem k_line : eq22 243 8 (mask 8) (GH.F 0) (LH.F 1) (LH.F 2) (GH.F 0) = true := by
  decide +kernel

theorem k_canon : allN 4 (fun k => Nat.beq (Nat.shiftRight (UH.F k) 11880) 0) = true ∧
    allN 5 (fun k => Nat.beq (Nat.shiftRight (GH.F k) 1944) 0) = true ∧
    allN 3 (fun k => Nat.beq (Nat.shiftRight (LH.F k) 1944) 0) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem k_img : (strictB (imgW 36 (encW Ly0.wordX)) fun ax =>
    strictB (imgW 256 (encW Ly0.wordY)) fun ay =>
    strictB (imgY 8) fun aw => imgK ax ay aw) = true := by
  decide +kernel

theorem k_agree : (strictB (encW Ly0.wordU1) fun e0 => strictB (encW Ly0.wordU2) fun e1 =>
    strictB (encW Ly0.wordU3) fun e2 => strictB (encW Ly0.wordU4) fun e3 =>
    strictB (encW (McLMultiplier.invW Ly0.wordU1)) fun f0 =>
    strictB (encW (McLMultiplier.invW Ly0.wordU2)) fun f1 =>
    strictB (encW (McLMultiplier.invW Ly0.wordU3)) fun f2 =>
    strictB (encW (McLMultiplier.invW Ly0.wordU4)) fun f3 =>
    agreeK e0 e1 e2 e3 f0 f1 f2 f3) = true := by
  decide +kernel

end CertificateChecks.KernelLy

end
