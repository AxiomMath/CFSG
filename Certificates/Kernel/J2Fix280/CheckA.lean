module

public import Certificates.Kernel.J2Fix280.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Fix280

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm)
open CFSG.RankThree.PartTwo.J2Residue.C280

theorem c111603Wn : Nat.beq words.size 280 = true := by quickRfl

theorem c111603Wc : wcChk words.toList 0 = true := by quickRfl

theorem c111603Y0 : Nat.beq (YT 0) (cjK (wK words[0]!) Z) = true := by quickRfl

theorem c111603I : Nat.beq (pinvS 315 9 (mask 9) (AB 0)) (AI 0) = true ∧
    Nat.beq (pinvS 315 9 (mask 9) (AB 1)) (AI 1) = true ∧
    Nat.beq (pinvS 315 9 (mask 9) Z) ZI = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem c111603A0 : allN 40 (fun j => rowT (j + 40 * 0)) = true := by quickRfl

theorem c111603A1 : allN 40 (fun j => rowT (j + 40 * 1)) = true := by quickRfl

theorem c111603A2 : allN 40 (fun j => rowT (j + 40 * 2)) = true := by quickRfl

theorem c111603A3 : allN 40 (fun j => rowT (j + 40 * 3)) = true := by quickRfl

theorem c111603A4 : allN 40 (fun j => rowT (j + 40 * 4)) = true := by quickRfl

theorem c111603A5 : allN 40 (fun j => rowT (j + 40 * 5)) = true := by quickRfl

theorem c111603A6 : allN 40 (fun j => rowT (j + 40 * 6)) = true := by quickRfl

end CertificateChecks.KernelJ2Fix280

end
