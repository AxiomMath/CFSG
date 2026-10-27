module

public import Certificates.Kernel.Item434.M22Chain
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

theorem m22W : szOK 22 5 = true := by quickRfl

theorem m22Perm : allN 13
    (fun j => permOK 22 5 (mask 5) (22 * 5) (M22C.S j) (M22C.SI j)) = true := by
  quickRfl

theorem m22SigB : ∀ j < 4, arrBind m22SigArrs[j]! 22 5 (M22C.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem m22SigP : allN 4 (fun j => permB 22 5 (M22C.S j)) = true := by quickRfl

theorem m22Orig : m22SigArrs.size = 4 ∧ ∀ j < 4, m22SigArrs[j]! = unpack 22 5 (M22C.S j) :=
  ⟨rfl, fun j hj => arrBind_sound (m22SigB j hj)⟩

theorem m22Binds : Binds 22 5 M22C.S 13 5 M22C.BP m22GenS (m22Base.map Fin.val).toArray := by
  obtain ⟨hs, he⟩ := CFSG.KC.O8.pushWords_eq m22Orig M22C.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> decide +kernel

theorem m22_chain : m22ChainCheck = true := by
  unfold m22ChainCheck
  rw [Bool.and_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · rw [CFSG.KC.O8.wordsOf_eq]
    exact rawChainK_sound (NS := 1) (CH := 22) m22Binds M22C.head M22C.hl (by norm_num) M22C.hs
  · rw [rawOrbitSizesK_sound m22Binds m22Perm M22C.hl]
    decide +kernel

theorem m22SiftP {g : Array ℕ} {G : ℕ} (hg : g = unpack 22 5 G)
    (h : (Nat.beq (Nat.shiftRight G (22 * 5)) 0 &&
      allN 22 (fun t => Nat.blt (pg 5 (mask 5) G t) 22) &&
      siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22C.LR M22C.TRI M22C.BP 5 0 G) = true) :
    siftA 22 m22Levels (m22Base.map Fin.val).toArray 0 g = true := by
  simp only [Bool.and_eq_true] at h
  exact siftK_soundR m22Binds m22Perm M22C.hl hg (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

theorem m22AB : arrBind m22GenA 22 5 (M22E 0) = true := by quickRfl
theorem m22BB : arrBind m22GenB 22 5 (M22E 1) = true := by quickRfl
theorem m22E1B : arrBind m22E1 22 5 (M22E 2) = true := by quickRfl
theorem m22E2B : arrBind m22E2 22 5 (M22E 3) = true := by quickRfl

theorem m22PP : permB 22 5 (M22E 2) = true ∧ permB 22 5 (M22E 3) = true :=
  ⟨by quickRfl, by quickRfl⟩

@[expose] noncomputable def m22SiftK (i : ℕ) : Bool :=
  Nat.beq (Nat.shiftRight (M22E i) (22 * 5)) 0 &&
    allN 22 (fun t => Nat.blt (pg 5 (mask 5) (M22E i) t) 22) &&
    siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22C.LR M22C.TRI M22C.BP 5 0 (M22E i)

theorem m22SiftK_all : ∀ i < 4, m22SiftK i = true := by
  intro i hi
  interval_cases i <;> quickRfl

theorem m22_sift : m22SiftCheck = true := by
  unfold m22SiftCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨m22SiftP (arrBind_sound m22AB) (m22SiftK_all 0 (by norm_num)),
    m22SiftP (arrBind_sound m22BB) (m22SiftK_all 1 (by norm_num))⟩,
    m22SiftP (arrBind_sound m22E1B) (m22SiftK_all 2 (by norm_num))⟩,
    m22SiftP (arrBind_sound m22E2B) (m22SiftK_all 3 (by norm_num))⟩

theorem m22_elt : m22EltCheck = true := by
  have p1 : Pk 22 5 m22E1 (M22E 2) := ⟨arrBind_sound m22E1B, m22PP.1⟩
  have p2 : Pk 22 5 m22E2 (M22E 3) := ⟨arrBind_sound m22E2B, m22PP.2⟩
  have ps : ∀ i < m22SigArrs.size, Pk 22 5 m22SigArrs[i]! (M22C.S i) := fun i hi =>
    ⟨m22Orig.2 i (by rw [m22Orig.1] at hi; exact hi),
      CFSG.KS.Raw.Orb.allN_iff.1 m22SigP i (by rw [m22Orig.1] at hi; exact hi)⟩
  unfold m22EltCheck
  rw [e9Check_pk m22W p1 p2, sigCheck_pk m22W ps m22Ords m22PExps p1 p2]
  decide +kernel

end CertificateChecks.KernelItem434

end
