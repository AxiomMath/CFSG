module

public import Certificates.Kernel.L34Cov.Syl3Checks
public import Certificates.Kernel.L34Cov.Lift22212

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.Certificates.L34Cov CFSG.CosetTable
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.GrS4
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W CFSG.KC.L34KSnd CFSG.KC.L34K
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W

theorem wK_eq (w : List ℕ) : Cn (wK w) ∧ wordTab w = unpack 42 6 (wK w) := by
  unfold wordTab wK
  rw [idTab42]
  exact pword_spec (gS GT) genT w _ cn_pidn fun j _ => genT_gS gensG j

theorem wReps_length : wReps.length = 105 := rfl

theorem yTab_eq {k : ℕ} (hk : k < 105) :
    wordTab (wReps.getD k []) = unpack 42 6 (CertificateChecks.KernelLC.L34PR.Y k) ∧
      Cn (CertificateChecks.KernelLC.L34PR.Y k) ∧
      invTab 42 (unpack 42 6 (CertificateChecks.KernelLC.L34PR.Y k)) =
        unpack 42 6 (CertificateChecks.KernelLC.L34PR.YI k) ∧
      Cn (CertificateChecks.KernelLC.L34PR.YI k) := by
  have hk' : k < wReps.length := by rw [wReps_length]; exact hk
  have hs : k < (wordTabs wReps).size := by simpa [wordTabs] using hk'
  have e : wordTab (wReps.getD k []) = (wordTabs wReps)[k]! := by
    rw [wordTabs, getElem!_pos _ k (by simpa using hk'), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hk']
  obtain ⟨e1, c1⟩ := gY.2 k hk
  have e2 := invY.1 k hk
  rw [map_get (invTab 42) hs, e1] at e2
  exact ⟨e.trans e1, c1, e2, (andB_iff.1 (allN' kYI k hk)).1⟩

theorem notIn_of {x : ℕ} (hx : Cn x)
    (h : allN 64 (fun q => CFSG.KLie.CT.notB (Nat.beq (CertificateChecks.KernelLC.L34PT.T q) x)) =
      true) :
    notInOK (pts 42 6 64 CertificateChecks.KernelLC.L34PT.T) (unpack 42 6 x) = true := by
  unfold notInOK
  rw [CFSG.PSL3Four.Native.allBelow, List.all_eq_true]
  intro k hk
  have hk' : k < 64 := by simpa [pts] using hk
  have h1 := allN' h k hk'
  rw [notB_iff] at h1
  rw [pts, pts_get hk', beq_unpack (rT.2.2.1 k hk') hx, h1]
  rfl

theorem notB_false {b : Bool} (h : CFSG.KLie.CT.notB b = false) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

theorem syl3WitOK_k : syl3WitOK = true := by
  unfold syl3WitOK
  dsimp only
  rw [rB.1, CFSG.PSL3Four.Native.allBelow, List.all_eq_true]
  intro k hk
  have hk' : k < 105 := by
    rw [List.mem_range, wReps_length] at hk
    exact hk
  obtain ⟨yE, yC, iE, iC⟩ := yTab_eq hk'
  rw [Bool.or_eq_true]
  rcases orB_iff.1 (allN' ch22900s_k k hk') with hn | hw
  · left
    unfold r3NotNormalizes r3Conj
    dsimp only
    obtain ⟨i, hi, hni⟩ := exists_of_notB_allN hn
    have h64 := notB_false hni
    obtain ⟨gE, gC⟩ := rT.2.2.2.2 i hi
    have zC : Cn (zK k) := CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp iC gT5.2) yC
    have hz : conjTab 42 (invTab 42 (wordTab (wReps.getD k []))) (wordTab (wReps.getD k [])) r₃T =
        unpack 42 6 (zK k) := by
      rw [yE, iE, gT5.1, conjTab, comp_unpack' iC gT5.2,
        comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp iC gT5.2) yC]
      rfl
    rw [hz, rT.1, anyBelow, List.any_eq_true]
    refine ⟨i, ?_, ?_⟩
    · rw [List.mem_range, rT.2.2.2.1]
      exact hi
    · rw [gE, conj_unpack zC gC]
      exact notIn_of (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp zC gC) zC) h64
  · right
    obtain ⟨e, he, hwe⟩ := List.any_eq_true.1 hw
    refine List.any_eq_true.2 ⟨e, he, ?_⟩
    unfold witK at hwe
    obtain ⟨h1, hx⟩ := andB_iff.1 hwe
    unfold witX at hx
    obtain ⟨hc, hx⟩ := andB_iff.1 hx
    obtain ⟨hxi, hx⟩ := andB_iff.1 hx
    obtain ⟨hinv, hmem⟩ := andB_iff.1 hx
    obtain ⟨xC, xE⟩ := wK_eq e.2
    have hinv' := Nat.eq_of_beq_eq_true hinv
    have xiE := invTab_eq_of_pcomp xC hxi hinv'
    have hio : invOK3 (wordTab e.2) = true := by
      unfold invOK3
      rw [xE, xiE, size_unpack, comp_unpack' hxi xC, pcomp_inv_of_pcomp xC hxi hinv', idTab42]
      simp
    rw [hio, xE, yE, xiE, gT5.1, comp_unpack' xC gT5.2, comp_unpack' gT5.2 xC,
      Nat.eq_of_beq_eq_true hc, comp_unpack' hxi yC, found_of hmem, beq_self_eq_true,
      Nat.eq_of_beq_eq_true h1, beq_self_eq_true]
    rfl

theorem facts22900 :
    (∀ s ∈ witSpecs, (PresentedGroup.mk _ (FreeGroup.mk s.1) : PG 2 coverWs) =
      PresentedGroup.mk _ (FreeGroup.mk (zword s.2.1 s.2.2.1 s.2.2.2))) ∧
    syl3WitOK = true := by
  refine ⟨fun s hs => ?_, syl3WitOK_k⟩
  change cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  rw [cv_zword]
  simp only [witSpecs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only
    rw [show alphaF witF = substWord (autWs uAF uBF) witF from rfl]
    exact (lift_eq ch22900l_F List.mem_cons_self).trans (by norm_num)
  · exact cv_eq_of_cvId ch22900l_sq.1
  · dsimp only
    rw [alphaG_eq]
    exact (lift_eq ch22900l_G List.mem_cons_self).trans (by norm_num)
  · exact cv_eq_of_cvId ch22900l_sq.2.1
  · dsimp only
    rw [alphaU_eq]
    exact (lift_eq ch22900l_U List.mem_cons_self).trans (by norm_num)
  · exact cv_eq_of_cvId ch22900l_sq.2.2

end CertificateChecks.KernelL34Cov

end
