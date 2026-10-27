
module

public import Certificates.Kernel.SporSch.HN.PtCR
public import Certificates.Kernel.SporSch.HN.Pt2086K
public import Certificates.Kernel.Sporadic.OddCore.HND1
public import Certificates.Kernel.Sporadic.OddCore.HN2093
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt2086

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.ONSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPtC CFSG.KD.HNPt2086 Matrix

local notation "OM" => ordMat 5 133 13 1729

noncomputable abbrev rK (k : ℕ) : ℕ := fldW CR (14 * k) 14

noncomputable abbrev ppK (K : ℕ) : ℕ := fldW CP (6 * (K + 1)) 6

noncomputable abbrev labK (K : ℕ) : ℕ := fldW CL (4 * (K + 1)) 4

theorem pw_data : ∀ i < 14, pcF i = pWords[i]!.map gcode ∧ (∀ c ∈ pcF i, c < 22) ∧
    ∀ l ∈ pWords[i]!, l ≠ 0 ∧ l.natAbs ≤ 11 := by
  decide +kernel

theorem chain_data : rK 0 = 0 ∧ ∀ K < 43, rK (K + 1) ≠ 0 ∧
    pparOf InvData.parRecs (rK (K + 1)) = rK (ppK K) ∧
    plabOf InvData.parRecs (rK (K + 1)) = labK K ∧ ppK K < K + 1 ∧ labK K < 14 := by
  rw [CertificateChecks.KernelSpor.HND.par_eq]
  decide +kernel

theorem wit_data : InvData.witRep.size = 39 ∧ InvData.witKer.size = 39 ∧
    InvData.witFix.size = 39 ∧ ∀ w < 39,
    fldW WK (Nat.mul 6 w) 6 < 44 ∧ fldW WK (Nat.mul 6 w) 6 ≤ InvData.witRep[w]! ∧
    rK (fldW WK (Nat.mul 6 w) 6) = InvData.witRep[w]! ∧
    fldW (fldW WQ (Nat.mul 21 w) 21) (21 * 0) 21 =
      (if InvData.witKer[w]! = 1 then fldW UT (21 * w) 21 else InvData.witFix[w]!) ∧
    fldW (fldW WF (Nat.mul 21 w) 21) (21 * 0) 21 = InvData.witFix[w]! ∧
    InvData.witFix[w]! < nPts ∧ fldW UT (21 * w) 21 < nPts ∧ fldW FT (21 * w) 21 = InvData.witFix[w]! :=
  by decide +kernel

theorem rep_data : pReps.size = 29 ∧ fldW FT (21 * 39) 21 = 1 ∧ fldW UT (21 * 39) 21 ≠ 1 ∧
    fldW UT (21 * 39) 21 < nPts ∧ (∀ i < InvData.nonRep.size, ∃ c < 29,
      pReps[c]! = InvData.nonRep[i]! ∧ InvData.nonRep.contains pReps[c]! = true) ∧
    ∀ c < 29, fldW KP (Nat.mul 6 c) 6 < 44 ∧ fldW KP (Nat.mul 6 c) 6 ≤ pReps[c]! ∧
    rK (fldW KP (Nat.mul 6 c) 6) = pReps[c]! ∧ fldW (PF c) (21 * 0) 21 = 1 ∧
    fldW (PF c) (21 * 1) 21 = fldW (PI c) (21 * 0) 21 ∧ fldW (PI c) (21 * 0) 21 < nPts ∧
    fldW (PI c) (21 * 1) 21 < nPts ∧
    (fldW (PI c) (21 * 1) 21 = 1 ↔ InvData.nonRep.contains pReps[c]! = false) := by
  rw [pReps, CertificateChecks.KernelSpor.HN2093.clsLists_eq]
  decide +kernel

theorem WT_mat {i : ℕ} (hi : i < 14) :
    Canon 5 133 13 (WT i) ∧ OM (WT i) = matR (wordG pWords[i]!) := by
  rw [← Nat.eq_of_beq_eq_true (allN_spec w_WT i hi)]
  obtain ⟨h1, h2⟩ := wordGT_mat _ (pw_data i hi).2.1
  refine ⟨h1, h2.trans ?_⟩
  rw [(pw_data i hi).1]
  rfl

theorem hT :
    ∀ j < 11, PRep hnsData.n gTabsJ[j]! (permR (genR j)) :=
  fun _ hj => prep_genTabs hj

theorem hTi :
    ∀ j < 11, PRep hnsData.n (pinvs nPts gTabsJ)[j]! (permR (genR j))⁻¹ :=
  fun _ hj => (prep_genTabs_inv hj).1

theorem chain :
    ∀ k < 44, Canon 5 133 13 (YT k) ∧ ∃ y : RH,
    OM (YT k) = matR y ∧ ∀ f, k ≤ f → ∀ x : X,
      evalLiftF gTabsJ (pinvs nPts gTabsJ) InvData.parRecs f (rK k) x = ((y • x : X) : ℕ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · have e : YT 0 = CFSG.KD.OrdHN.ONE := Nat.eq_of_beq_eq_true one_YT
      refine ⟨by rw [e]; exact (one_sound CFSG.KD.OrdHN.consts).1, 1,
        by rw [e, HNXP.one_ord, matR_one], fun f _ x => ?_⟩
      rw [chain_data.1, one_smul]
      cases f <;> rfl
    · obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      obtain ⟨d1, d2, d3, d4, d5⟩ := chain_data.2 K (by omega)
      obtain ⟨c1, y1, m1, e1⟩ := ih (ppK K) d4 (by omega)
      obtain ⟨cW, mW⟩ := WT_mat d5
      have eY : YT (K + 1) = CFSG.KC.LL.HN.mm (WT (labK K)) (YT (ppK K)) :=
        (Nat.eq_of_beq_eq_true (allN_spec chain_YT K (by omega))).symm
      refine ⟨by rw [eY]; exact (HNXP.mm_sound cW c1).1, wordG pWords[labK K]! * y1,
        by rw [eY, (HNXP.mm_sound cW c1).2, mW, m1, matR_mul], fun f hf x => ?_⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [evalLiftF, if_neg d1, d2, d3, e1 f' (by omega) x,
        evalWordPt_eq hT hTi _ (pw_data _ d5).2.2 (y1 • x), mul_smul]

theorem lift_pts
    {k r : ℕ} (hk : k < 44) (hr : rK k = r) (hkr : k ≤ r) {FL IL c : ℕ}
    (hc : c ≤ 64) (h : ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M
      (trM (YT k)) FL IL c = true) {i : ℕ} (hi : i < c) (h1 : fldW FL (21 * i) 21 < nPts)
    (h2 : fldW IL (21 * i) 21 < nPts) :
    evalLift gTabsJ (pinvs nPts gTabsJ) InvData.parRecs r (fldW FL (21 * i) 21) =
      fldW IL (21 * i) 21 := by
  obtain ⟨cY, y, mY, eY⟩ := chain k hk
  subst hr
  have := eY (rK k) hkr ⟨_, h1⟩
  rw [evalLift, this]
  exact ri_pts cY mY hc h hi h1 h2

theorem t4_pts {i : ℕ} (hi : i < 40)
    (h1 : fldW FT (21 * i) 21 < nPts) (h2 : fldW UT (21 * i) 21 < nPts) :
    (arrJ t4J)[fldW FT (21 * i) 21]! = fldW UT (21 * i) 21 := by
  rw [arrJ_get _ h1, gi_of_lt _ h1, ← jR_smul]
  exact ri_pts T4_mat.1 (by rw [T4_mat.2, matR_jR]) (by norm_num) p_T4 hi h1 h2

theorem allBelowN_false {n : ℕ} {p : ℕ → Bool} {i : ℕ} (hi : i < n) (h : p i = false) :
    allBelowN n p = false := by
  cases e : allBelowN n p
  · rfl
  · rw [allBelowN_spec e hi] at h
    exact absurd h (by decide)

theorem lift_main :
    liftChecksT nPts gTabsJ (pinvs nPts gTabsJ) (arrJ t4J) InvData.parRecs = true := by
  obtain ⟨s1, s2, s3, wd⟩ := wit_data
  obtain ⟨rs, ft1, ut1, ut1l, nr, rd⟩ := rep_data
  unfold liftChecksT
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨gTabsJ_size, pinvs_size.trans gTabsJ_size⟩,
    allBelowN_iff.2 fun j hj => (prep_genTabs_inv hj).2⟩, s1⟩, s2⟩, s3⟩, ?_⟩, ?_⟩, ?_⟩
  · refine allBelowN_iff.2 fun w hw => ?_
    obtain ⟨k1, k2, k3, q1, q2, f1, u1, ft⟩ := wd w hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨f1, ?_⟩
    have hq : (if InvData.witKer[w]! = 1 then (arrJ t4J)[InvData.witFix[w]!]!
        else InvData.witFix[w]!) = fldW (fldW WQ (Nat.mul 21 w) 21) (21 * 0) 21 := by
      rw [q1]
      split_ifs
      · rw [← ft, t4_pts (by omega) (by rw [ft]; exact f1) u1]
      · rfl
    have hql : fldW (fldW WQ (Nat.mul 21 w) 21) (21 * 0) 21 < nPts := by
      rw [q1]
      split_ifs
      · exact u1
      · exact f1
    rw [hq, lift_pts k1 k3 k2 (by norm_num) (allN_spec p_wits w hw) (by norm_num) hql
      (by rw [q2]; exact f1), q2]
  · refine allBelowN_iff.2 fun i hi => ?_
    obtain ⟨c, hc, hce, hn⟩ := nr i hi
    obtain ⟨k1, k2, k3, a0, a1, al, bl, hb⟩ := rd c hc
    have hb1 : fldW (PI c) (21 * 1) 21 ≠ 1 := fun h => by
      rw [hb.1 h] at hn
      exact absurd hn (by decide)
    have e0 := lift_pts k1 k3 k2 (by norm_num) (allN_spec p_reps c hc) (i := 0) (by norm_num)
      (by rw [a0]; decide) al
    have e1 := lift_pts k1 k3 k2 (by norm_num) (allN_spec p_reps c hc) (i := 1) (by norm_num)
      (by rw [a1]; exact al) bl
    rw [a0] at e0
    rw [a1] at e1
    rw [Bool.not_eq_true']
    refine allBelowN_false (i := 1) (by decide) ?_
    rw [← hce, e0, e1]
    exact beq_eq_false_iff_ne.2 hb1
  · refine allBelowN_iff.2 fun c hc => ?_
    obtain ⟨k1, k2, k3, a0, a1, al, bl, hb⟩ := rd c hc
    cases hn : InvData.nonRep.contains pReps[c]!
    · rw [Bool.false_or, Bool.not_eq_true']
      have e0 := lift_pts k1 k3 k2 (by norm_num) (allN_spec p_reps c hc) (i := 0) (by norm_num)
        (by rw [a0]; decide) al
      have e1 := lift_pts k1 k3 k2 (by norm_num) (allN_spec p_reps c hc) (i := 1) (by norm_num)
        (by rw [a1]; exact al) bl
      rw [a0] at e0
      rw [a1] at e1
      refine allBelowN_false (i := 1) (by decide) ?_
      have t1 := t4_pts (i := 39) (by norm_num) (by rw [ft1]; decide) ut1l
      rw [ft1] at t1
      rw [t1, e0, e1, hb.2 hn]
      simp [ut1]
    · rfl

theorem liftChecks_ok :
    liftChecksO (hnsData.orbit ()) = true := by
  unfold liftChecksO liftChecksR liftChecksS
  rw [← hRegs_eq, ← hStrongArr_eq, HNCTab.cTab_eq, hStrongArr_SJ, hns_n, natTab_alpha, natTab_beta]
  have h := lift_main
  rw [← pword_SJ letters_c4.2.2.2.2] at h
  exact h

end CertificateChecks.KernelSporSch.HNPt2086

end
