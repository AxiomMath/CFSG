module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

@[expose] def autD : List (List Int) :=
  [[2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -2], [2, -1, 2, -1, 2, 1, -2, 1, -2, 1, -2],
    [-1, 2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -2, 1], [-3, -5, 3, 5, 3],
    [-5, -3, -4, -3, -5, 4, 3, 4, 5, 3, 4]]

end CertificateChecks.KernelJ2Cover

#ks_rawchain CertificateChecks.KernelJ2Cover.PA 315 9 16 CFSG.ComponentClassification.J2Cover.autStrong
  CFSG.ComponentClassification.J2Cover.autBase 2 CertificateChecks.KernelJ2Cover.autD

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem perm : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (PA.S j) (PA.SI j)) = true := by
  quickRfl

theorem binds : Binds 315 9 PA.S 7 3 PA.BP autStrong autBase := by
  have hs : Nat.beq autStrong.size 7 = true := by quickRfl
  have hb : Nat.beq autBase.size 3 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem words_eq : autWords = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 autD := by
  decide

theorem autChain : rawChainOK 315 (autStrong.extract 0 2) autStrong autBase autWords 4 = true ∧
    rawOrbitSizes 315 autStrong autBase = [315, 160, 12] := by
  refine ⟨?_, ?_⟩
  · rw [words_eq]
    exact rawChainK_sound (NS := 20) (CH := 16) binds PA.head PA.hl (by norm_num) PA.hs
  · rw [rawOrbitSizesK_sound binds perm PA.hl]
    decide

theorem inP_of {t : Array Nat} {G : Nat} (ht : t = unpack 315 9 G)
    (hz : Nat.beq (Nat.shiftRight G (315 * 9)) 0 = true)
    (hr : allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315) = true)
    (hs : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PA.LR PA.TRI PA.BP 3 0 G = true) :
    inP t = true := by
  unfold inP autLevels
  exact siftK_soundR binds perm PA.hl ht (Nat.eq_of_beq_eq_true hz) hr hs

end CertificateChecks.KernelJ2Cover

end
