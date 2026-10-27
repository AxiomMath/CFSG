module

public import Certificates.Kernel.J2Cover.AutChain
public import Certificates.Kernel.J2Cover.TxtKernel
public import CFSG.Certificates.Kernel.DecTextSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelData
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

@[expose] def crAD : List (List Int) := [[-2, -1], [-3, 4, 3]]

@[expose] def crTD : List (List Int) := [[-2, -1, -2, -1], [1, 1, 1, -2], [4, -5], [-1, -3, 6, 2, 1]]

@[expose] def crUD : List (List Int) := [[-2, -2, -1, 2, 1], [-1, 4, 1], [-2, -5, -2, 3]]

end CertificateChecks.KernelJ2Cover

#ks_rawchain CertificateChecks.KernelJ2Cover.CRA 315 9 16
  CFSG.ComponentClassification.J2Cover.Kernel.crAStrong
  CFSG.ComponentClassification.J2Cover.Kernel.crABase 3 CertificateChecks.KernelJ2Cover.crAD

#ks_rawchain CertificateChecks.KernelJ2Cover.CRT 315 9 16
  CFSG.ComponentClassification.J2Cover.Kernel.crTStrong
  CFSG.ComponentClassification.J2Cover.Kernel.crTBase 3 CertificateChecks.KernelJ2Cover.crTD

#ks_rawchain CertificateChecks.KernelJ2Cover.CRU 315 9 16
  CFSG.ComponentClassification.J2Cover.Kernel.crUStrong
  CFSG.ComponentClassification.J2Cover.Kernel.crUBase 3 CertificateChecks.KernelJ2Cover.crUD

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.ComponentClassification.J2Cover.Kernel
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Co3.Native (wordsArr)
open CFSG.KC.DecText TxtKernel

theorem bind_txt {a : Array Nat} {s : String} {cs : List Char} {P : Nat}
    (ha : a = CFSG.Sporadic.Fi23.Native.natsOf s) (hs : s = String.ofList cs)
    (hd : digitsOK cs = true) (hb : arrBind (natsK cs).toArray 315 9 P = true) :
    a = unpack 315 9 P := by
  rw [ha, hs, natsOf_ofList hd]
  exact arrBind_sound hb

theorem crA_perm : allN 5 (fun j => permOK 315 9 (mask 9) (315 * 9) (CRA.S j) (CRA.SI j)) = true := by
  quickRfl

theorem crA_binds : Binds 315 9 CRA.S 5 2 CRA.BP crAStrong crABase := by
  have hs : Nat.beq crAStrong.size 5 = true := by quickRfl
  have hb : Nat.beq crABase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j
  · exact arrBind_sound (by quickRfl)
  · exact arrBind_sound (by quickRfl)
  · exact arrBind_sound (by quickRfl)
  · exact bind_txt rfl C.crAStrong.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crAStrong.e1 (by quickRfl) (by quickRfl)

theorem crA_chain : rawChainOK 315 (crAStrong.extract 0 3) crAStrong crABase crAWords 4 = true ∧
    rawOrbitSizes 315 crAStrong crABase = [120, 4] := by
  refine ⟨?_, ?_⟩
  · have e : crAWords = wordsArr 3 5 crAD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) crA_binds CRA.head CRA.hl (by norm_num) CRA.hs
  · rw [rawOrbitSizesK_sound crA_binds crA_perm CRA.hl]
    decide

theorem crT_perm : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (CRT.S j) (CRT.SI j)) = true := by
  quickRfl

theorem crT_binds : Binds 315 9 CRT.S 7 3 CRT.BP crTStrong crTBase := by
  have hs : Nat.beq crTStrong.size 7 = true := by quickRfl
  have hb : Nat.beq crTBase.size 3 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j
  · exact arrBind_sound (by quickRfl)
  · exact arrBind_sound (by quickRfl)
  · exact bind_txt rfl C.crTStrong.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crTStrong.e1 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crTStrong.e2 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crTStrong.e3 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crTStrong.e4 (by quickRfl) (by quickRfl)

theorem crT_chain : rawChainOK 315 (crTStrong.extract 0 3) crTStrong crTBase crTWords 4 = true ∧
    rawOrbitSizes 315 crTStrong crTBase = [160, 8, 3] := by
  refine ⟨?_, ?_⟩
  · have e : crTWords = wordsArr 3 7 crTD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) crT_binds CRT.head CRT.hl (by norm_num) CRT.hs
  · rw [rawOrbitSizesK_sound crT_binds crT_perm CRT.hl]
    decide

theorem crU_perm : allN 6 (fun j => permOK 315 9 (mask 9) (315 * 9) (CRU.S j) (CRU.SI j)) = true := by
  quickRfl

theorem crU_binds : Binds 315 9 CRU.S 6 2 CRU.BP crUStrong crUBase := by
  have hs : Nat.beq crUStrong.size 6 = true := by quickRfl
  have hb : Nat.beq crUBase.size 2 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j
  · exact arrBind_sound (by quickRfl)
  · exact arrBind_sound (by quickRfl)
  · exact arrBind_sound (by quickRfl)
  · exact bind_txt rfl C.crUStrong.e0 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crUStrong.e1 (by quickRfl) (by quickRfl)
  · exact bind_txt rfl C.crUStrong.e2 (by quickRfl) (by quickRfl)

theorem crU_chain : rawChainOK 315 (crUStrong.extract 0 3) crUStrong crUBase crUWords 4 = true ∧
    rawOrbitSizes 315 crUStrong crUBase = [42, 16] := by
  refine ⟨?_, ?_⟩
  · have e : crUWords = wordsArr 3 6 crUD := by decide
    rw [e]
    exact rawChainK_sound (NS := 20) (CH := 16) crU_binds CRU.head CRU.hl (by norm_num) CRU.hs
  · rw [rawOrbitSizesK_sound crU_binds crU_perm CRU.hl]
    decide

end CertificateChecks.KernelJ2Cover

end
