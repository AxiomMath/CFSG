module

public import Certificates.Kernel.Item434.J2Chain
public import Certificates.Kernel.J2Cover.AutChain
public import CFSG.Certificates.Kernel.Item434.PkSound
public import CFSG.Certificates.Kernel.O8ConstrSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
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
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (xArr zArr)

theorem j2W : szOK 315 9 = true := by quickRfl

theorem j2Perm : allN 8 (fun j => permOK 315 9 (mask 9) (315 * 9) (J2C.S j) (J2C.SI j)) = true := by
  quickRfl

theorem j2SigB : ∀ j < 3, arrBind j2SigArrs[j]! 315 9 (J2C.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem j2SigP : allN 3 (fun j => permB 315 9 (J2C.S j)) = true := by quickRfl

theorem j2Orig : j2SigArrs.size = 3 ∧ ∀ j < 3, j2SigArrs[j]! = unpack 315 9 (J2C.S j) :=
  ⟨rfl, fun j hj => arrBind_sound (j2SigB j hj)⟩

theorem j2Binds : Binds 315 9 J2C.S 8 4 J2C.BP j2GenS (j2Base.map Fin.val).toArray := by
  obtain ⟨hs, he⟩ := CFSG.KC.O8.pushWords_eq j2Orig J2C.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> decide +kernel

theorem j2_chain : j2ChainCheck = true := by
  unfold j2ChainCheck
  rw [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [CFSG.KC.O8.wordsOf_eq]
    exact rawChainK_sound (NS := 5) (CH := 64) j2Binds J2C.head J2C.hl (by norm_num) J2C.hs
  · rw [rawOrbitSizesK_sound j2Binds j2Perm J2C.hl]
    decide +kernel

theorem j2SiftP {g : Array ℕ} {G : ℕ} (hg : g = unpack 315 9 G)
    (h : (Nat.beq (Nat.shiftRight G (315 * 9)) 0 &&
      allN 315 (fun t => Nat.blt (pg 9 (mask 9) G t) 315) &&
      siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2C.LR J2C.TRI J2C.BP 4 0 G) = true) :
    siftA 315 j2Levels (j2Base.map Fin.val).toArray 0 g = true := by
  simp only [Bool.and_eq_true] at h
  exact siftK_soundR j2Binds j2Perm J2C.hl hg (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

theorem j2ZB : arrBind zArr 315 9 (J2E 0) = true := by quickRfl
theorem j2XB : arrBind xArr 315 9 (J2E 1) = true := by quickRfl

theorem j2PP : permB 315 9 (J2E 0) = true ∧ permB 315 9 (J2E 1) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem kJA : (Nat.beq (Nat.shiftRight (KernelJ2Cover.PA.S 0) (315 * 9)) 0 &&
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (KernelJ2Cover.PA.S 0) t) 315) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2C.LR J2C.TRI J2C.BP 4 0
      (KernelJ2Cover.PA.S 0)) = true := by
  quickRfl
theorem kJB : (Nat.beq (Nat.shiftRight (KernelJ2Cover.PA.S 1) (315 * 9)) 0 &&
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (KernelJ2Cover.PA.S 1) t) 315) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2C.LR J2C.TRI J2C.BP 4 0
      (KernelJ2Cover.PA.S 1)) = true := by
  quickRfl
theorem kJZ : (Nat.beq (Nat.shiftRight (J2E 0) (315 * 9)) 0 &&
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (J2E 0) t) 315) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2C.LR J2C.TRI J2C.BP 4 0 (J2E 0)) = true := by
  quickRfl
theorem kJX : (Nat.beq (Nat.shiftRight (J2E 1) (315 * 9)) 0 &&
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (J2E 1) t) 315) &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2C.LR J2C.TRI J2C.BP 4 0 (J2E 1)) = true := by
  quickRfl

theorem j2_sift : j2SiftCheck = true := by
  have a0 := KernelJ2Cover.binds.2.2.2.2.1 0 (by norm_num)
  have a1 := KernelJ2Cover.binds.2.2.2.2.1 1 (by norm_num)
  unfold j2SiftCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨j2SiftP a0 kJA, j2SiftP a1 kJB⟩, j2SiftP (arrBind_sound j2ZB) kJZ⟩,
    j2SiftP (arrBind_sound j2XB) kJX⟩

theorem j2_elt : j2EltCheck = true := by
  have p1 : Pk 315 9 zArr (J2E 0) := ⟨arrBind_sound j2ZB, j2PP.1⟩
  have p2 : Pk 315 9 xArr (J2E 1) := ⟨arrBind_sound j2XB, j2PP.2⟩
  have ps : ∀ i < j2SigArrs.size, Pk 315 9 j2SigArrs[i]! (J2C.S i) := fun i hi =>
    ⟨j2Orig.2 i (by rw [j2Orig.1] at hi; exact hi),
      CFSG.KS.Raw.Orb.allN_iff.1 j2SigP i (by rw [j2Orig.1] at hi; exact hi)⟩
  unfold j2EltCheck
  rw [e9Check_pk j2W p1 p2, sigCheck_pk j2W ps j2Ords j2PExps p1 p2]
  decide +kernel

end CertificateChecks.KernelItem434

end
