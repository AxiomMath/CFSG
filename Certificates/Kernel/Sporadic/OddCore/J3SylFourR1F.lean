module

public import Certificates.Kernel.Sporadic.OddCore.J3SylFourR1
public import Certificates.Kernel.Sporadic.OddCore.J3HypSylF
public import Certificates.Kernel.Sporadic.OddCore.SylFourRows

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3SylFourR1

open CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem base : szOK 6156 13 = true ∧ cK (pidn 6156 13) = true ∧
    allN 4 (fun j => bAnd(cK (J3R1S.GI j), bAnd(Nat.beq (J3R1S.GI j) (J3HypP (Nat.add j 4)),
      Nat.beq (J3R1S.G j) (pidn 6156 13)))) = true ∧
    Nat.beq J3R1S.cnt 32 = true ∧ penumHdK (pidn 6156 13) J3R1S.cnt 32 J3R1S.T J3R1S.PL = true := by
  simpa only [bAnd_iff] using r1Base

theorem hcnt : J3R1S.cnt = 32 := Nat.eq_of_beq_eq_true base.2.2.2.1

theorem gen {j : Nat} (hj : j < 4) : cK (J3R1S.GI j) = true ∧ J3R1S.GI j = J3HypP (j + 4) ∧
    J3R1S.G j = pidn 6156 13 := by
  have h := allN_spec base.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem sg_eq : CFSG.EvenSporadicStandard.HypOne.J3.sgR1 =
    ((List.range 4).map fun j => tabT (unpack 6156 13 (J3R1S.GI j))).toArray := by
  unfold CFSG.EvenSporadicStandard.HypOne.J3.sgR1
  rw [J3HypSyl.hyp_tab (by norm_num), J3HypSyl.hyp_tab (by norm_num), J3HypSyl.hyp_tab (by norm_num),
    J3HypSyl.hyp_tab (by norm_num), ← (gen (j := 0) (by norm_num)).2.1,
    ← (gen (j := 1) (by norm_num)).2.1, ← (gen (j := 2) (by norm_num)).2.1,
    ← (gen (j := 3) (by norm_num)).2.1]
  rfl

theorem s_tabs : TabsOK 6156 13 4 J3R1S.GI CFSG.EvenSporadicStandard.HypOne.J3.sgR1 := by
  refine ⟨by rw [sg_eq]; simp, fun j hj => ⟨?_, (gen hj).1⟩⟩
  rw [sg_eq, getElem!_pos _ j (by simpa using hj)]
  simp

theorem s_pe : ∀ i < J3R1S.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true J3R1S.G J3R1S.GI 4
    J3R1S.cnt J3R1S.T J3R1S.PL J3R1S.POS J3R1S.SRT J3R1S.SRI i = true :=
  fun i hi => penumSl_spec r1Enum i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < J3R1S.cnt,
    hsortPtK 6156 13 (mask 13) J3R1S.cnt J3R1S.T J3R1S.HS J3R1S.HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq]
  exact slK_spec r1Sort i (Nat.zero_le _) (by omega) hi

theorem r1_mul :
    mulClosureH 6156 CFSG.EvenSporadicStandard.HypOne.J3.sgR1 32 =
        hRec 6156 13 J3R1S.cnt J3R1S.T J3R1S.PL ∧
      mulTreeOK 6156 CFSG.EvenSporadicStandard.HypOne.J3.sgR1
        (hRec 6156 13 J3R1S.cnt J3R1S.T J3R1S.PL).1 (hRec 6156 13 J3R1S.cnt J3R1S.T J3R1S.PL).2.1
        (hRec 6156 13 J3R1S.cnt J3R1S.T J3R1S.PL).2.2 = true ∧
      hkeysDistinct 6156 (hRec 6156 13 J3R1S.cnt J3R1S.T J3R1S.PL).1.toList = true :=
  mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2 s_pe s_hs

theorem hT {i : Nat} (hi : i < 32) : canonK 6156 13 (mask 13) (6156 * 13) (J3R1S.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

theorem cgR1_lo {l : Nat} (hl : l < 3) :
    cgR1 l = J3CentP (l + 22) ∧ cgR1I l = J3CentI (l + 22) := by
  have hb : Nat.blt l (nat_lit 3) = true := Nat.blt_eq.mpr hl
  refine ⟨?_, ?_⟩
  · unfold cgR1
    rw [hb]
  · unfold cgR1I
    rw [hb]

theorem cgR1_perm {l : Nat} (hl : l < 4) :
    invEqK 6156 13 (mask 13) (6156 * 13) (cgR1 l) (cgR1I l) = true := by
  rcases Nat.lt_or_ge l 3 with h | h
  · rw [(cgR1_lo h).1, (cgR1_lo h).2]
    exact j3_perm (by omega)
  · obtain rfl : l = 3 := by omega
    exact j3_perm (k := 21) (by norm_num)

theorem cgR1_get {j : Nat} (hj : j < 4) :
    CFSG.EvenSporadicStandard.HypOne.J3.cgR1[j]! = tabT (unpack 6156 13 (cgR1 j)) := by
  rcases Nat.lt_or_ge j 3 with h | h
  · rw [(cgR1_lo h).1, ← tbl_unpack (by omega), CFSG.EvenSporadicStandard.HypOne.J3.cgR1,
      getElem!_pos _ j (by simpa using hj)]
    interval_cases j
    all_goals simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · obtain rfl : j = 3 := by omega
    rw [CFSG.EvenSporadicStandard.HypOne.J3.cgR1, getElem!_pos _ 3 (by simp)]
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [CFSG.EvenSporadicStandard.HypOne.J3.t1, tbl_unpack (by norm_num)]
    rfl

theorem cgR1_tabs : TabsOK 6156 13 4 cgR1 CFSG.EvenSporadicStandard.HypOne.J3.cgR1 :=
  ⟨rfl, fun j hj => ⟨cgR1_get hj, (canonK_of_invEqK base.1 (cgR1_perm hj)).1⟩⟩

theorem r1_row {i : Nat} (hi : i < 32) : r1Row i = true := by
  rcases Nat.lt_or_ge i 16 with h0 | h0
  · exact slK_spec r1Five0 i (by omega) (by omega) hi
  · exact slK_spec r1Five1 i h0 (by omega) hi

theorem r1_rows : (mulClosureH 6156 CFSG.EvenSporadicStandard.HypOne.J3.sgR1 32).1.all
    (fun s => !ordTest 6156 4 s || CFSG.EvenSporadicStandard.HypOne.fiveConjOK 6156 6
      CFSG.EvenSporadicStandard.HypOne.J3.cgR1
      (CFSG.EvenSporadicStandard.HypOne.J3.cgR1.map (invT 6156)) s) = true := by
  rw [r1_mul.1]
  change (Array.ofFn (n := J3R1S.cnt) fun i => tabT (unpack 6156 13 (J3R1S.T i.val))).all _ = true
  refine sylRows_all (k := 4) (f := 2) (G := cgR1) (GI := cgR1I) (by norm_num) base.1
    (by norm_num) base.2.1 cgR1_tabs (fun l hl => cgR1_perm hl)
    (fun i hi => hT (by rw [← hcnt]; exact hi)) (fun i hi hc => ?_)
  have hr := r1_row (by rw [← hcnt]; exact hi)
  unfold r1Row at hr
  simp only [CFSG.KS.PF.strictB_eqP] at hr
  unfold rowR1 at hr
  simp only [CFSG.KS.PF.strictB_eqP] at hr
  exact row_imp hr hc

end CertificateChecks.KernelSpor.J3SylFourR1

end
