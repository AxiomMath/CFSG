module

public import Certificates.Kernel.Sporadic.OddCore.J3SylFourR
public import Certificates.Kernel.Sporadic.OddCore.J3OutSylF
public import Certificates.Kernel.Sporadic.OddCore.SylFourRows

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3SylFourR

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.EvenSporadicStandard.Fin76b.J3
open CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.OddCore

theorem cgR_lo {l : Nat} (hl : l < 5) : cgR l = J3CentP (l + 10) ∧ cgRI l = J3CentI (l + 10) := by
  have hb : Nat.blt l (nat_lit 5) = true := Nat.blt_eq.mpr hl
  refine ⟨?_, ?_⟩
  · unfold cgR
    rw [hb]
  · unfold cgRI
    rw [hb]

theorem cgR_perm {l : Nat} (hl : l < 6) :
    invEqK 6156 13 (mask 13) (6156 * 13) (cgR l) (cgRI l) = true := by
  rcases Nat.lt_or_ge l 5 with h | h
  · rw [(cgR_lo h).1, (cgR_lo h).2]
    exact j3_perm (by omega)
  · obtain rfl : l = 5 := by omega
    exact r0Inv

theorem cgR_get {j : Nat} (hj : j < 6) : cgR0[j]! = tabT (unpack 6156 13 (cgR j)) := by
  rcases Nat.lt_or_ge j 5 with h | h
  · rw [(cgR_lo h).1, ← tbl_unpack (by omega), cgR0, getElem!_pos _ j (by simpa using hj)]
    interval_cases j
    all_goals simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · obtain rfl : j = 5 := by omega
    rw [cgR0, getElem!_pos _ 5 (by simp)]
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [z0, J3HypSyl.hyp_tab (by norm_num)]
    rfl

theorem cgR_tabs : TabsOK 6156 13 6 cgR cgR0 :=
  ⟨rfl, fun _ hj => ⟨cgR_get hj, (canonK_of_invEqK J3OutSyl.base.1 (cgR_perm hj)).1⟩⟩

theorem r0_slice {k : Nat} (hk : k < 16) : slK 256 r0Row (16 * k) 16 = true := by
  interval_cases k
  exacts [r0Five0, r0Five1, r0Five2, r0Five3, r0Five4, r0Five5, r0Five6, r0Five7, r0Five8,
    r0Five9, r0Five10, r0Five11, r0Five12, r0Five13, r0Five14, r0Five15]

theorem r0_row {i : Nat} (hi : i < 256) : r0Row i = true :=
  slK_spec (r0_slice (k := i / 16) (by omega)) i (by omega) (by omega) hi

theorem rowC_tree {s c L : Nat} (hs : canonK 6156 13 (mask 13) (6156 * 13) s = true)
    (h : rowC (pidn 6156 13) s c L = true)
    (hc : (Nat.beq (pcomp 6156 13 (mask 13) (pcomp 6156 13 (mask 13) s s)
        (pcomp 6156 13 (mask 13) s s)) (pidn 6156 13) &&
      !Nat.beq (pcomp 6156 13 (mask 13) s s) (pidn 6156 13) && !Nat.beq s (pidn 6156 13)) = true) :
    CFSG.KS.HBfs.FiveTree (hkeyB 6156 13 (mask 13)) (cjK 6156 13 (mask 13) cgR cgRI) 6 2 [s] := by
  unfold rowC at h
  rw [bIf_eqF] at h
  cases h1 : Nat.beq c 1
  · rw [h1, Bool.cond_false, bIf_eqF] at h
    cases h0 : Nat.beq c 0
    · rw [h0, Bool.cond_false, bIf_eqF] at h
      cases h4 : Nat.blt c 4
      · rw [h4, Bool.cond_false] at h
        unfold rowR at h
        simp only [CFSG.KS.PF.strictB_eqP] at h
        rw [← hkeyU_eq_hkeyB]
        exact fiveTopK_sound _ _ _ _ _ (row_imp h hc)
      · rw [h4, Bool.cond_true, bIf_eqF] at h
        have hx : Nat.sub c (nat_lit 2) < 6156 := by
          have := Nat.blt_eq.mp h4
          have : c - 2 < 6156 := by omega
          exact this
        cases e : Nat.beq (pt4 s (Nat.sub c (nat_lit 2))) (Nat.sub c (nat_lit 2))
        · rw [pow4_ne_of_pt hs hx e, Bool.false_and, Bool.false_and] at hc
          exact Bool.noConfusion hc
        · rw [e, Bool.cond_true] at h
          exact Bool.noConfusion h
    · rw [h0, Bool.cond_true] at h
      rw [h, Bool.not_true, Bool.and_false, Bool.false_and] at hc
      exact Bool.noConfusion hc
  · rw [h1, Bool.cond_true] at h
    exact fiveTree_of_fiveTopE h

theorem r0_rows : (mulClosureH 6156 j3SylowGenTbls.toArray 256).1.all (fun s => !ordTest 6156 4 s ||
    CFSG.EvenSporadicStandard.HypOne.fiveConjOK 6156 6 cgR0 (cgR0.map (invT 6156)) s) = true := by
  have hc := J3OutSyl.closure_eq
  unfold sylXGens at hc
  rw [hc]
  change (Array.ofFn (n := J3XS.cnt) fun i => tabT (unpack 6156 13 (J3XS.T i.val))).all _ = true
  refine sylRows_allT (k := 6) (f := 2) (G := cgR) (GI := cgRI) (by norm_num) J3OutSyl.base.1
    (by norm_num) J3OutSyl.hidc cgR_tabs (fun l hl => cgR_perm hl)
    (fun i hi => J3OutSyl.hT (by rw [← J3OutSyl.hcnt]; exact hi)) (fun i hi hc => ?_)
  have hr := r0_row (by rw [← J3OutSyl.hcnt]; exact hi)
  unfold r0Row at hr
  simp only [CFSG.KS.PF.strictB_eqP] at hr
  exact rowC_tree (J3OutSyl.hT (by rw [← J3OutSyl.hcnt]; exact hi)) hr hc

end CertificateChecks.KernelSpor.J3SylFourR

end
