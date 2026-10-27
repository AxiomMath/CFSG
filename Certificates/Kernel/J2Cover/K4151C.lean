module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.J2Cover.K4151D
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
meta import Certificates.Kernel.J2Cover.K4151D
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

@[expose] def nilD4151 : List (List Int) := []

end CertificateChecks.KernelJ2Cover

#ks_rawchain CertificateChecks.KernelJ2Cover.SB 315 9 16 CertificateChecks.KernelJ2Cover.subStrong
  CertificateChecks.KernelJ2Cover.subBase 5 CertificateChecks.KernelJ2Cover.nilD4151

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem sb_perm : allN 5 (fun j => permOK 315 9 (mask 9) (315 * 9) (SB.S j) (SB.SI j)) = true := by
  quickRfl

theorem sb_binds : Binds 315 9 SB.S 5 2 SB.BP subStrong subBase := by
  have hs : Nat.beq subStrong.size 5 = true := by quickRfl
  have hb : Nat.beq subBase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem sbChain : rawChainOK 315 (subStrong.extract 0 5) subStrong subBase
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 5 nilD4151) 4 = true ∧
    rawOrbitSizes 315 subStrong subBase = [160, 12] := by
  refine ⟨?_, ?_⟩
  · exact rawChainK_sound (NS := 20) (CH := 16) sb_binds SB.head SB.hl (by norm_num) SB.hs
  · rw [rawOrbitSizesK_sound sb_binds sb_perm SB.hl]
    decide

end CertificateChecks.KernelJ2Cover

end
