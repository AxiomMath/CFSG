module

public import Certificates.Kernel.J2Cover.KerChains
public import Certificates.Kernel.J2Cover.TxtExternal
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

@[expose] def fixCD : List (List Int) := [[-2, 1, 1], [1, -2, 1, 2, 1]]

@[expose] def nilD : List (List Int) := []

end CertificateChecks.KernelJ2Cover

#ks_rawchain CertificateChecks.KernelJ2Cover.FC 315 9 16
  CFSG.ComponentClassification.J2Cover.External.fixCStrong
  CFSG.ComponentClassification.J2Cover.External.fixCBase 2 CertificateChecks.KernelJ2Cover.fixCD

#ks_rawchain CertificateChecks.KernelJ2Cover.FD 315 9 16
  CFSG.ComponentClassification.J2Cover.External.fixDStrong
  CFSG.ComponentClassification.J2Cover.External.fixDBase 2 CertificateChecks.KernelJ2Cover.nilD

#ks_rawchain CertificateChecks.KernelJ2Cover.FW 315 9 16
  CFSG.ComponentClassification.J2Cover.External.fixWStrong
  CFSG.ComponentClassification.J2Cover.External.fixWBase 2 CertificateChecks.KernelJ2Cover.nilD

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.ComponentClassification.J2Cover.External
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Co3.Native (wordsArr)
open TxtExternal

theorem fC_perm : allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (FC.S j) (FC.SI j)) = true := by
  quickRfl

theorem fC_binds : Binds 315 9 FC.S 4 2 FC.BP fixCStrong fixCBase := by
  have hs : Nat.beq fixCStrong.size 4 = true := by quickRfl
  have hb : Nat.beq fixCBase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j
  · exact bind_txt rfl C.fixCStrong.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.fixCStrong.e1 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.fixCStrong.e2 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.fixCStrong.e3 (by quickRfl) (by quickRfl)

theorem fC_chain : rawChainOK 315 (fixCStrong.extract 0 2) fixCStrong fixCBase fixCWords 4 = true ∧
    rawOrbitSizes 315 fixCStrong fixCBase = [21, 16] := by
  refine ⟨?_, ?_⟩
  · have e : fixCWords = wordsArr 2 4 fixCD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) fC_binds FC.head FC.hl (by norm_num) FC.hs
  · rw [rawOrbitSizesK_sound fC_binds fC_perm FC.hl]
    decide

theorem fD_perm : allN 2 (fun j => permOK 315 9 (mask 9) (315 * 9) (FD.S j) (FD.SI j)) = true := by
  quickRfl

theorem fD_binds : Binds 315 9 FD.S 2 1 FD.BP fixDStrong fixDBase := by
  have hs : Nat.beq fixDStrong.size 2 = true := by quickRfl
  have hb : Nat.beq fixDBase.size 1 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j
  · exact bind_txt rfl C.fixDStrong.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.fixDStrong.e1 (by quickRfl) (by quickRfl)

theorem fD_chain : rawChainOK 315 (fixDStrong.extract 0 2) fixDStrong fixDBase fixDWords 4 = true ∧
    rawOrbitSizes 315 fixDStrong fixDBase = [168] := by
  refine ⟨?_, ?_⟩
  · have e : fixDWords = wordsArr 2 2 nilD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) fD_binds FD.head FD.hl (by norm_num) FD.hs
  · rw [rawOrbitSizesK_sound fD_binds fD_perm FD.hl]
    decide

theorem fW_perm : allN 2 (fun j => permOK 315 9 (mask 9) (315 * 9) (FW.S j) (FW.SI j)) = true := by
  quickRfl

theorem fW_binds : Binds 315 9 FW.S 2 1 FW.BP fixWStrong fixWBase := by
  have hs : Nat.beq fixWStrong.size 2 = true := by quickRfl
  have hb : Nat.beq fixWBase.size 1 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j
  · exact bind_txt rfl C.fixWStrong.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.fixWStrong.e1 (by quickRfl) (by quickRfl)

theorem fW_chain : rawChainOK 315 (fixWStrong.extract 0 2) fixWStrong fixWBase fixWWords 4 = true ∧
    rawOrbitSizes 315 fixWStrong fixWBase = [8] := by
  refine ⟨?_, ?_⟩
  · have e : fixWWords = wordsArr 2 2 nilD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) fW_binds FW.head FW.hl (by norm_num) FW.hs
  · rw [rawOrbitSizesK_sound fW_binds fW_perm FW.hl]
    decide

end CertificateChecks.KernelJ2Cover

end
