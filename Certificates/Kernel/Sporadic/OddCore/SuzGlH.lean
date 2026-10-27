module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlF
public import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000
set_option Elab.async false

#kon_slices CertificateChecks.KernelSpor.SuzGl.rhoSl 0 12

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG CertificateChecks.KernelSpor.SuzC1EZ

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem rhoK_of {i : Nat} (hi : i < 192) : rhoK (SuzC1EQ.T i) = true := by
  have h : ∀ s < 12, rhoSl s = true := by
    intro s hs
    interval_cases s
    exacts [rhoSl0, rhoSl1, rhoSl2, rhoSl3, rhoSl4, rhoSl5, rhoSl6, rhoSl7, rhoSl8, rhoSl9,
      rhoSl10, rhoSl11]
  have := allBlk_spec (h (i / 16) (by omega)) (i % 16) (by omega)
  rwa [show Nat.add (Nat.mul 16 (i / 16)) (i % 16) = i by
    change 16 * (i / 16) + i % 16 = i
    omega] at this

theorem a4_tabs {j : Nat} (hj : j < 12) : a4Enum.tabs[j]! = unpack 1782 11 (SuzC1EA.T j) := by
  rw [a4E.1]
  exact ofFn_get (fun i => unpack 1782 11 (SuzC1EA.T i)) (by rw [kCnt.2]; exact hj)

theorem a4_size : a4Enum.tabs.size = 12 := by
  rw [a4E.1]
  simp [penumRec, kCnt.2]

theorem a4_canon {j : Nat} (hj : j < 12) : cn (SuzC1EA.T j) = true :=
  penumPt_canon (ptA j (by rw [kCnt.2]; exact hj))

theorem memA_iff {X : Nat} : memA X = true ↔ ∃ j < 12, SuzC1EA.T j = X := by
  unfold memA
  constructor
  · intro h
    by_contra hn
    have : allN 12 (fun j => Bool.not (Nat.beq (SuzC1EA.T j) X)) = true := by
      refine CFSG.KS.PEnum.allN_of fun j hj => ?_
      have hne : SuzC1EA.T j ≠ X := fun e => hn ⟨j, hj, e⟩
      simp [beq_false hne]
    rw [this] at h
    exact absurd h (by decide)
  · rintro ⟨j, hj, e⟩
    cases h : allN 12 (fun j => Bool.not (Nat.beq (SuzC1EA.T j) X))
    · rfl
    · have := allN_spec h j hj
      simp [e] at this

theorem found_a4 {X : Nat} (hX : cn X = true) :
    found (indexOf a4Enum.tabs) a4Enum.tabs (unpack 1782 11 X) = memA X := by
  apply Bool.eq_iff_iff.2
  rw [found_indexOf_iff, memA_iff, a4_size]
  constructor
  · rintro ⟨j, hj, e⟩
    rw [a4_tabs hj] at e
    refine ⟨j, hj, Nat.eq_of_beq_eq_true ?_⟩
    rw [← CFSG.KS.PEnum.beq_unpack (a4_canon hj) hX, e]
    exact beq_self_eq_true _
  · rintro ⟨j, hj, e⟩
    exact ⟨j, hj, by rw [a4_tabs hj, e]⟩

theorem rhoBody_eq {c : Tab} {X : Nat} (hc : P c X) :
    (!(comp 1782 c (comp 1782 c c) == idTab 1782 && !(c == idTab 1782) &&
        comp 1782 (conjTab 1782 c (comp 1782 c c) w0T) w0T ==
          comp 1782 w0T (conjTab 1782 c (comp 1782 c c) w0T) &&
        !(conjTab 1782 c (comp 1782 c c) w0T == w0T) &&
        conjTab 1782 c (comp 1782 c c) (conjTab 1782 c (comp 1782 c c) w0T) ==
          comp 1782 w0T (conjTab 1782 c (comp 1782 c c) w0T)) ||
      found (indexOf a4Enum.tabs) a4Enum.tabs c) = rhoK X := by
  have pcc := pc' hc hc
  have pu : P (conjTab 1782 c (comp 1782 c c) w0T) (pc (pc X (SuzTwG 6)) (pc X X)) := by
    unfold conjTab
    exact pc' (pc' hc pw0) pcc
  have pv : P (conjTab 1782 c (comp 1782 c c) (conjTab 1782 c (comp 1782 c c) w0T))
      (pc (pc X (pc (pc X (SuzTwG 6)) (pc X X))) (pc X X)) := by
    conv_lhs => unfold conjTab
    exact pc' (pc' hc pu) pcc
  rw [beqP (pc' hc pcc) pId', beqP hc pId', beqP (pc' pu pw0) (pc' pw0 pu), beqP pu pw0,
    beqP pv (pc' pw0 pu), hc.1, found_a4 hc.2]
  unfold rhoK
  rw [strictB_app', strictB_app']
  simp only [Bool.and_assoc]
  rfl

end CertificateChecks.KernelSpor.SuzGl

end
