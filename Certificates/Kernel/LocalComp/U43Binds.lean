module

public import Certificates.Kernel.LocalComp.U43Chains
public import Certificates.Kernel.Multipliers.U43BFacts
public import CFSG.Certificates.Kernel.O8ConstrSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.U43

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.O8
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.EvenSmallLie.Child3.SelU43
open CFSG.LieType.Multipliers.U43
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

theorem kAC0 : Nat.beq (UA.S 0) (CertificateChecks.KernelU43B.C.S 0) = true := by quickRfl
theorem kAC1 : Nat.beq (UA.S 1) (CertificateChecks.KernelU43B.C.S 1) = true := by quickRfl

theorem a_0 : autGens[0]! = unpack 820 10 (UA.S 0) := by
  rw [Nat.eq_of_beq_eq_true kAC0]
  exact CertificateChecks.KernelU43B.binds.2.2.2.2.1 0 (by omega)

theorem a_1 : autGens[1]! = unpack 820 10 (UA.S 1) := by
  rw [Nat.eq_of_beq_eq_true kAC1]
  exact CertificateChecks.KernelU43B.binds.2.2.2.2.1 1 (by omega)
theorem dEnt : ∀ j : Fin 820,
    (ptIndex fun k => if k = 0 then (⟨0, 1⟩ : F9) * decode j.val k else decode j.val k) =
      pg 10 (mask 10) (UA.S 2) j.val := by decide +kernel

theorem sEnt : ∀ j : Fin 820,
    (ptIndex fun k => decode j.val k * decode j.val k * decode j.val k) =
      pg 10 (mask 10) (UA.S 3) j.val := by decide +kernel

theorem a_2 : autGens[2]! = unpack 820 10 (UA.S 2) := by
  change deltaArr = _
  unfold deltaArr unpack
  exact congrArg _ (funext dEnt)

theorem a_3 : autGens[3]! = unpack 820 10 (UA.S 3) := by
  change sigmaArr = _
  unfold sigmaArr unpack
  exact congrArg _ (funext sEnt)

theorem a_orig : autGens.size = 4 ∧ ∀ j < 4, autGens[j]! = unpack 820 10 (UA.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  exacts [a_0, a_1, a_2, a_3]

theorem bindsUA : Binds 820 10 UA.S 10 5 UA.BP autS autBaseArr := by
  obtain ⟨hs, he⟩ := pushWords_eq a_orig UA.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem permUA : allN 10 (fun j => permOK 820 10 (mask 10) (820 * 10) (UA.S j) (UA.SI j)) = true := by
  quickRfl

theorem kSG : allN 4 (fun j => wordEqK 820 10 (mask 10) (pidn 820 10) UA.S UA.SI 10
    (sylowGenWords.getD j []) (US.S j)) = true := by quickRfl

theorem sg_orig : sylowGens.size = 4 ∧ ∀ j < 4, sylowGens[j]! = unpack 820 10 (US.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  have h := wordEqK_sound (S := autS) ⟨bindsUA.2.2.2.1, bindsUA.2.2.2.2.1⟩ permUA
    (allN_spec kSG j hj)
  have hl : j < sylowGenWords.length := by
    have : sylowGenWords.length = 4 := rfl
    omega
  have e : sylowGens[j]! = autW (sylowGenWords.getD j []) := by
    simp [sylowGens, getElem!_def, hl, List.getD_eq_getElem?_getD]
  rw [e, autW]
  exact h.1

theorem bindsUS : Binds 820 10 US.S 6 2 US.BP sylowS sylowBaseArr := by
  obtain ⟨hs, he⟩ := pushWords_eq sg_orig US.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem permUS : allN 6 (fun j => permOK 820 10 (mask 10) (820 * 10) (US.S j) (US.SI j)) = true := by
  quickRfl

end CertificateChecks.KernelLC.U43

end
