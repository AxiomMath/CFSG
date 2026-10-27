module

public import Certificates.Kernel.LocalComp.L39Chains
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

namespace CertificateChecks.KernelLC.L39

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.O8
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.EvenSmallLie.Child3.SelL39
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

theorem t1_0 : (#[pA, pB] : Array (Array Nat))[0]! = unpack 91 7 (LT1.S 0) := by decide +kernel
theorem t1_1 : (#[pA, pB] : Array (Array Nat))[1]! = unpack 91 7 (LT1.S 1) := by decide +kernel
theorem t_0 : (#[qA, qB] : Array (Array Nat))[0]! = unpack 182 8 (LT.S 0) := by decide +kernel
theorem t_1 : (#[qA, qB] : Array (Array Nat))[1]! = unpack 182 8 (LT.S 1) := by decide +kernel
theorem a_0 : autGens[0]! = unpack 182 8 (LA.S 0) := by decide +kernel
theorem a_1 : autGens[1]! = unpack 182 8 (LA.S 1) := by decide +kernel
theorem a_2 : autGens[2]! = unpack 182 8 (LA.S 2) := by decide +kernel
theorem a_3 : autGens[3]! = unpack 182 8 (LA.S 3) := by decide +kernel

theorem t1_orig : (#[pA, pB] : Array (Array Nat)).size = 2 ∧
    ∀ j < 2, (#[pA, pB] : Array (Array Nat))[j]! = unpack 91 7 (LT1.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  exacts [t1_0, t1_1]

theorem t_orig : (#[qA, qB] : Array (Array Nat)).size = 2 ∧
    ∀ j < 2, (#[qA, qB] : Array (Array Nat))[j]! = unpack 182 8 (LT.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  exacts [t_0, t_1]

theorem a_orig : autGens.size = 4 ∧ ∀ j < 4, autGens[j]! = unpack 182 8 (LA.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  exacts [a_0, a_1, a_2, a_3]

theorem bindsLT1 : Binds 91 7 LT1.S 7 5 LT1.BP t1S t1BaseArr := by
  obtain ⟨hs, he⟩ := pushWords_eq t1_orig LT1.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem bindsLT : Binds 182 8 LT.S 7 5 LT.BP tS tBaseArr := by
  obtain ⟨hs, he⟩ := pushWords_eq t_orig LT.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem bindsLA : Binds 182 8 LA.S 15 6 LA.BP autS autBaseArr := by
  obtain ⟨hs, he⟩ := pushWords_eq a_orig LA.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem permLA : allN 15 (fun j => permOK 182 8 (mask 8) (182 * 8) (LA.S j) (LA.SI j)) = true := by
  quickRfl

theorem kSG : allN 4 (fun j => wordEqK 182 8 (mask 8) (pidn 182 8) LA.S LA.SI 15
    (sylowGenWords.getD j []) (LS.S j)) = true := by quickRfl

theorem sg_orig : sylowGens.size = 4 ∧ ∀ j < 4, sylowGens[j]! = unpack 182 8 (LS.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  have h := wordEqK_sound (S := autS) ⟨bindsLA.2.2.2.1, bindsLA.2.2.2.2.1⟩ permLA
    (allN_spec kSG j hj)
  have hl : j < sylowGenWords.length := by
    have : sylowGenWords.length = 4 := rfl
    omega
  have e : sylowGens[j]! = autW (sylowGenWords.getD j []) := by
    simp [sylowGens, getElem!_def, hl, List.getD_eq_getElem?_getD]
  rw [e, autW]
  exact h.1

theorem bindsLS : Binds 182 8 LS.S 8 2 LS.BP sylowS sylowBaseArr := by
  obtain ⟨hs, he⟩ := pushWords_eq sg_orig LS.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

end CertificateChecks.KernelLC.L39

end
