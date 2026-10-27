module

public import Certificates.Kernel.Item434.HSChain
public import Certificates.Kernel.HS100.Chain
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.O8ConstrSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelItem434

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Item434
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CertificateChecks.KernelHS100 (hs100Arr_eq)

theorem hsW : szOK 100 7 = true := by quickRfl

theorem hsPerm : allN 12 (fun j => permOK 100 7 (mask 7) (100 * 7) (HSC.S j) (HSC.SI j)) = true := by
  quickRfl

theorem hsSigB : ∀ j < 3, arrBind hsSigArrs[j]! 100 7 (HSC.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem hsSigP : allN 3 (fun j => permB 100 7 (HSC.S j)) = true := by quickRfl

theorem hsOrig : hsSigArrs.size = 3 ∧ ∀ j < 3, hsSigArrs[j]! = unpack 100 7 (HSC.S j) :=
  ⟨rfl, fun j hj => arrBind_sound (hsSigB j hj)⟩

theorem hsBinds : Binds 100 7 HSC.S 12 5 HSC.BP hsGenS (hsBase.map Fin.val).toArray := by
  obtain ⟨hs, he⟩ := CFSG.KC.O8.pushWords_eq hsOrig HSC.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> decide +kernel

theorem hs_chain : hsChainCheck = true := by
  unfold hsChainCheck
  rw [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [CFSG.KC.O8.wordsOf_eq]
    exact rawChainK_sound (NS := 1) (CH := 100) hsBinds HSC.head HSC.hl (by norm_num) HSC.hs
  · rw [rawOrbitSizesK_sound hsBinds hsPerm HSC.hl]
    decide +kernel

theorem hsSiftP {g : Array ℕ} {G : ℕ} (hg : g = unpack 100 7 G)
    (h : (Nat.beq (Nat.shiftRight G (100 * 7)) 0 &&
      allN 100 (fun t => Nat.blt (pg 7 (mask 7) G t) 100) &&
      siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HSC.LR HSC.TRI HSC.BP 5 0 G) = true) :
    siftA 100 hsLevels (hsBase.map Fin.val).toArray 0 g = true := by
  simp only [Bool.and_eq_true] at h
  exact siftK_soundR hsBinds hsPerm HSC.hl hg (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

theorem hsE1B : arrBind hsE1 100 7 (HSE 0) = true := by quickRfl
theorem hsE2B : arrBind hsE2 100 7 (HSE 1) = true := by quickRfl

theorem hsPP : permB 100 7 (KernelHS100.HP.F 0) = true ∧ permB 100 7 (KernelHS100.HP.F 1) = true ∧
    permB 100 7 (HSE 0) = true ∧ permB 100 7 (HSE 1) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem kA : (Nat.beq (Nat.shiftRight (KernelHS100.HP.F 0) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (KernelHS100.HP.F 0) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HSC.LR HSC.TRI HSC.BP 5 0 (KernelHS100.HP.F 0)) = true := by
  quickRfl
theorem kB : (Nat.beq (Nat.shiftRight (KernelHS100.HP.F 1) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (KernelHS100.HP.F 1) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HSC.LR HSC.TRI HSC.BP 5 0 (KernelHS100.HP.F 1)) = true := by
  quickRfl
theorem kE1 : (Nat.beq (Nat.shiftRight (HSE 0) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (HSE 0) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HSC.LR HSC.TRI HSC.BP 5 0 (HSE 0)) = true := by
  quickRfl
theorem kE2 : (Nat.beq (Nat.shiftRight (HSE 1) (100 * 7)) 0 &&
    allN 100 (fun t => Nat.blt (pg 7 (mask 7) (HSE 1) t) 100) &&
    siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HSC.LR HSC.TRI HSC.BP 5 0 (HSE 1)) = true := by
  quickRfl

theorem hs_sift : hsSiftCheck = true := by
  have a0 := hs100Arr_eq 0 (by norm_num)
  have a1 := hs100Arr_eq 1 (by norm_num)
  have e1 := arrBind_sound hsE1B
  have e2 := arrBind_sound hsE2B
  unfold hsSiftCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [a0]
    exact isInvA_pk ⟨rfl, hsPP.1⟩
  · rw [a1]
    exact isInvA_pk ⟨rfl, hsPP.2.1⟩
  · exact hsSiftP a0 kA
  · exact hsSiftP a1 kB
  · exact hsSiftP e1 kE1
  · exact hsSiftP e2 kE2

theorem hs_elt : hsEltCheck = true := by
  have p1 : Pk 100 7 hsE1 (HSE 0) := ⟨arrBind_sound hsE1B, hsPP.2.2.1⟩
  have p2 : Pk 100 7 hsE2 (HSE 1) := ⟨arrBind_sound hsE2B, hsPP.2.2.2⟩
  have ps : ∀ i < hsSigArrs.size, Pk 100 7 hsSigArrs[i]! (HSC.S i) := fun i hi =>
    ⟨hsOrig.2 i (by rw [hsOrig.1] at hi; exact hi),
      CFSG.KS.Raw.Orb.allN_iff.1 hsSigP i (by rw [hsOrig.1] at hi; exact hi)⟩
  unfold hsEltCheck
  rw [e9Check_pk hsW p1 p2, sigCheck_pk hsW ps hsOrds hsPExps p1 p2]
  decide +kernel

end CertificateChecks.KernelItem434

end
