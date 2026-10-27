module

public import Certificates.Kernel.J2Cover.AutChain
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

@[expose] def c2BD : List (List Int) := [[-2, -1], [-1, -1, -1, -2, 1, 3, 2, 1]]

@[expose] def c2AD : List (List Int) := [[-2, -1, -2, -1], [1, 1, 1, -2], [3, -4]]

@[expose] def cOuD : List (List Int) := [[-2, -2, -1, 2, 1], [-1, 3, 1]]

@[expose] def sylD : List (List Int) := [[-1, -3, -1, 3], [-2, -1, -2, 3, 1, 2]]

end CertificateChecks.KernelJ2Cover

#ks_rawchain CertificateChecks.KernelJ2Cover.C2B 315 9 16
  CFSG.ComponentClassification.J2Cover.cent2BStrong
  CFSG.ComponentClassification.J2Cover.cent2BBase 2 CertificateChecks.KernelJ2Cover.c2BD

#ks_rawchain CertificateChecks.KernelJ2Cover.C2A 315 9 16
  CFSG.ComponentClassification.J2Cover.cent2AStrong
  CFSG.ComponentClassification.J2Cover.cent2ABase 2 CertificateChecks.KernelJ2Cover.c2AD

#ks_rawchain CertificateChecks.KernelJ2Cover.COU 315 9 16
  CFSG.ComponentClassification.J2Cover.centOuterStrong
  CFSG.ComponentClassification.J2Cover.centOuterBase 2 CertificateChecks.KernelJ2Cover.cOuD

#ks_rawchain CertificateChecks.KernelJ2Cover.SYL 315 9 16
  CFSG.ComponentClassification.J2Cover.sylowStrong
  CFSG.ComponentClassification.J2Cover.sylowBase 3 CertificateChecks.KernelJ2Cover.sylD

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Co3.Native (wordsArr)

theorem c2B_perm : allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (C2B.S j) (C2B.SI j)) = true := by
  quickRfl

theorem c2B_binds : Binds 315 9 C2B.S 4 2 C2B.BP cent2BStrong cent2BBase := by
  have hs : Nat.beq cent2BStrong.size 4 = true := by quickRfl
  have hb : Nat.beq cent2BBase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem c2B_chain :
    rawChainOK 315 (cent2BStrong.extract 0 2) cent2BStrong cent2BBase cent2BWords 4 = true ∧
      rawOrbitSizes 315 cent2BStrong cent2BBase = [60, 4] := by
  refine ⟨?_, ?_⟩
  · have e : cent2BWords = wordsArr 2 4 c2BD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) c2B_binds C2B.head C2B.hl (by norm_num) C2B.hs
  · rw [rawOrbitSizesK_sound c2B_binds c2B_perm C2B.hl]
    decide

theorem c2A_perm : allN 5 (fun j => permOK 315 9 (mask 9) (315 * 9) (C2A.S j) (C2A.SI j)) = true := by
  quickRfl

theorem c2A_binds : Binds 315 9 C2A.S 5 3 C2A.BP cent2AStrong cent2ABase := by
  have hs : Nat.beq cent2AStrong.size 5 = true := by quickRfl
  have hb : Nat.beq cent2ABase.size 3 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem c2A_chain :
    rawChainOK 315 (cent2AStrong.extract 0 2) cent2AStrong cent2ABase cent2AWords 4 = true ∧
      rawOrbitSizes 315 cent2AStrong cent2ABase = [160, 4, 3] := by
  refine ⟨?_, ?_⟩
  · have e : cent2AWords = wordsArr 2 5 c2AD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) c2A_binds C2A.head C2A.hl (by norm_num) C2A.hs
  · rw [rawOrbitSizesK_sound c2A_binds c2A_perm C2A.hl]
    decide

theorem cOu_perm : allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (COU.S j) (COU.SI j)) = true := by
  quickRfl

theorem cOu_binds : Binds 315 9 COU.S 4 2 COU.BP centOuterStrong centOuterBase := by
  have hs : Nat.beq centOuterStrong.size 4 = true := by quickRfl
  have hb : Nat.beq centOuterBase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem cOu_chain :
    rawChainOK 315 (centOuterStrong.extract 0 2) centOuterStrong centOuterBase centOuterWords 4 =
      true ∧ rawOrbitSizes 315 centOuterStrong centOuterBase = [42, 8] := by
  refine ⟨?_, ?_⟩
  · have e : centOuterWords = wordsArr 2 4 cOuD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) cOu_binds COU.head COU.hl (by norm_num) COU.hs
  · rw [rawOrbitSizesK_sound cOu_binds cOu_perm COU.hl]
    decide

theorem syl_perm : allN 5 (fun j => permOK 315 9 (mask 9) (315 * 9) (SYL.S j) (SYL.SI j)) = true := by
  quickRfl

theorem syl_binds : Binds 315 9 SYL.S 5 2 SYL.BP sylowStrong sylowBase := by
  have hs : Nat.beq sylowStrong.size 5 = true := by quickRfl
  have hb : Nat.beq sylowBase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem syl_chain :
    rawChainOK 315 (sylowStrong.extract 0 3) sylowStrong sylowBase sylowWords 4 = true ∧
      rawOrbitSizes 315 sylowStrong sylowBase = [64, 4] := by
  refine ⟨?_, ?_⟩
  · have e : sylowWords = wordsArr 3 5 sylD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) syl_binds SYL.head SYL.hl (by norm_num) SYL.hs
  · rw [rawOrbitSizesK_sound syl_binds syl_perm SYL.hl]
    decide

end CertificateChecks.KernelJ2Cover

end
