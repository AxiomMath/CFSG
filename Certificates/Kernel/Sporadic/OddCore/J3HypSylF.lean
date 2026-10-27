module

public import Certificates.Kernel.Sporadic.OddCore.J3HypSyl
public import CFSG.Certificates.Kernel.Spor.MulHFSound
public import Certificates.Kernel.Sporadic.OddCore.J3FourGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3HypSyl

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.EvenSporadicStandard.Fin76b.J3
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KS.Join
open CertificateChecks.KernelSpor.OddCore

theorem base : szOK 6156 13 = true ∧ cK (pidn 6156 13) = true ∧
    CFSG.KS.Prim.idK 6156 13 (mask 13) = true ∧ cK (J3CentP 9) = true ∧
    allN 3 (fun j => bAnd(cK (J3HS.GI j), bAnd(Nat.beq (J3HS.GI j) (J3HypP (Nat.add j 1)),
      Nat.beq (J3HS.G j) (pidn 6156 13)))) = true ∧
    Nat.beq J3HS.cnt 128 = true ∧ penumHdK (pidn 6156 13) J3HS.cnt 128 J3HS.T J3HS.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := base.2.1

theorem hid : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem hcnt : J3HS.cnt = 128 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.1

theorem gen {j : Nat} (hj : j < 3) : cK (J3HS.GI j) = true ∧ J3HS.GI j = J3HypP (j + 1) ∧
    J3HS.G j = pidn 6156 13 := by
  have h := allN_spec base.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem hyp_tab {k : Nat} (hk : k < 12) : hypTbl k = tabT (unpack 6156 13 (J3HypP k)) := by
  have h := hexT_join_sound (d := 4) (n₀ := 513) (w := 13) (c := 12) (N := 12) J3HypT.all hyp_join
    (by norm_num) k hk
  rw [← J3HypT.eq] at h
  rw [← tabT_natArr (hypTbl k)]
  exact congrArg tabT h

theorem sg_eq : sgP0 = ((List.range 3).map fun j => tabT (unpack 6156 13 (J3HS.GI j))).toArray := by
  unfold sgP0
  rw [hyp_tab (by norm_num), hyp_tab (by norm_num), hyp_tab (by norm_num),
    ← (gen (j := 0) (by norm_num)).2.1, ← (gen (j := 1) (by norm_num)).2.1,
    ← (gen (j := 2) (by norm_num)).2.1]
  rfl

theorem s_tabs : TabsOK 6156 13 3 J3HS.GI sgP0 := by
  refine ⟨by rw [sg_eq]; simp, fun j hj => ⟨?_, (gen hj).1⟩⟩
  rw [sg_eq, getElem!_pos _ j (by simpa using hj)]
  simp

theorem s_pe : ∀ i < J3HS.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true J3HS.G J3HS.GI 3
    J3HS.cnt J3HS.T J3HS.PL J3HS.POS J3HS.SRT J3HS.SRI i = true :=
  fun i hi => penumSl_spec sE i (Nat.zero_le _) (by omega) hi

theorem s_hs : ∀ i < J3HS.cnt,
    hsortPtK 6156 13 (mask 13) J3HS.cnt J3HS.T J3HS.HS J3HS.HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq 6156 13 J3HS.cnt J3HS.T J3HS.HS J3HS.HSI i]
  exact slK_spec sHF i (Nat.zero_le _) (by omega) hi

theorem centerKF_eq {t : Nat} (ht : t >>> (6156 * 13) = 0) : centerKF t = centerK t := by
  unfold centerKF centerK pc
  simp only [eq22_pcomp _ _ (by norm_num : (6156 : Nat) < 2 ^ 32) (by norm_num : 0 < 13),
    eq2_pcomp _ _ (by norm_num : (6156 : Nat) < 2 ^ 32) (by norm_num : 0 < 13) ht]

theorem center_ok : centerK (J3CentP 9) = true := by
  rw [← centerKF_eq (CFSG.KS.PF.canon_facts base.2.2.2.1).2.2.1]
  exact center_okF

theorem closure_eq : (mulClosureH 6156 sgP0 128).1 = (hRec 6156 13 J3HS.cnt J3HS.T J3HS.PL).1 := by
  rw [(mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2.2.2 s_pe s_hs).1]

@[expose] noncomputable def fE (i : Nat) : Table := tabT (unpack 6156 13 (J3HS.T i))

theorem syl_eq : sylList = ((List.range 128).map fE).toArray := by
  unfold sylList
  rw [closure_eq]
  apply Array.toList_inj.1
  simp only [hRec, Array.toList_ofFn, List.toList_toArray]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, hcnt]
  rfl

theorem hT {i : Nat} (hi : i < 128) : canonK 6156 13 (mask 13) (6156 * 13) (J3HS.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

theorem t0_eq : t0 = tabT (unpack 6156 13 (J3CentP 9)) := tbl_unpack (by norm_num)

theorem any_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem all_mem {l : List Nat} {p q : Nat → Bool} (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem facts24591 : j3CenterCheck = true := by
  have h := center_ok
  unfold centerK at h
  unfold j3CenterCheck
  rw [syl_eq, sg_eq, t0_eq]
  simp only [List.any_toArray, List.all_toArray, List.any_map, List.all_map, Function.comp]
  have h9 := base.2.2.2.1
  refine (congrArg₂ (· && ·) (congrArg₂ (· && ·) ?_ ?_) ?_).trans h
  · refine any_mem fun i hi => ?_
    simp only [Function.comp_apply, fE]
    rw [tblEq_unpack (hT (List.mem_range.1 hi)) h9]
  · refine all_mem fun i hi => ?_
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply, fE]
    rw [tblEq_unpack (hT hi') h9, hid, tblEq_unpack (hT hi') hidc]
    refine congrArg (fun b => !b || Nat.beq (J3HS.T i) (pidn 6156 13) || Nat.beq (J3HS.T i) (J3CentP 9))
      (all_mem fun j hj => ?_)
    simp only [Function.comp_apply]
    rw [commTT_unpack (hT hi') (gen (List.mem_range.1 hj)).1]
    rfl
  · refine any_mem fun i hi => ?_
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply, fE]
    rw [compT_unpack (hT hi') (hT hi'), tblEq_unpack (canonK_pcomp (hT hi') (hT hi')) h9]
    rfl

end CertificateChecks.KernelSpor.J3HypSyl

end
