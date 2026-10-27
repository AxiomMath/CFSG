module

public import Certificates.Kernel.Sporadic.OddCore.J3OutSyl
public import Certificates.Kernel.Sporadic.OddCore.J3HypSylF
public import Certificates.Kernel.SporSch.J3K426.Sift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ3Check

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3OutSyl

open CFSG.EvenSporadicStandard.HypOne.J3 CFSG.EvenSporadicStandard.Fin76b.J3
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.J3HypSyl (any_mem all_mem)

theorem base : szOK 6156 13 = true ∧ cK (pidn 6156 13) = true ∧
    CFSG.KS.Prim.idK 6156 13 (mask 13) = true ∧ cK (J3CentP 9) = true ∧
    allN 8 (fun j => bAnd(cK (J3XS.GI j), bAnd(Nat.beq (J3XS.GI j) (J3CentP (Nat.add j 1)),
      Nat.beq (J3XS.G j) (pidn 6156 13)))) = true ∧
    Nat.beq J3XS.cnt 256 = true ∧ penumHdK (pidn 6156 13) J3XS.cnt 256 J3XS.T J3XS.PL = true := by
  simpa only [bAnd_iff] using base_ok

theorem hidc : canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := base.2.1

theorem hid : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, idK_sound base.2.2.1]

theorem hcnt : J3XS.cnt = 256 := Nat.eq_of_beq_eq_true base.2.2.2.2.2.1

theorem gen {j : Nat} (hj : j < 8) : cK (J3XS.GI j) = true ∧ J3XS.GI j = J3CentP (j + 1) ∧
    J3XS.G j = pidn 6156 13 := by
  have h := allN_spec base.2.2.2.2.1 j hj
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem sg_eq : sylXGens = ((List.range 8).map fun j => tabT (unpack 6156 13 (J3XS.GI j))).toArray := by
  have h : ∀ j ∈ List.range 8, j3CentTbl (j + 1) = tabT (unpack 6156 13 (J3XS.GI j)) := by
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [(gen hj').2.1, tbl_unpack (by omega)]
  unfold sylXGens j3SylowGenTbls
  rw [List.map_congr_left h]

theorem s_tabs : TabsOK 6156 13 8 J3XS.GI sylXGens := by
  refine ⟨by rw [sg_eq]; simp, fun j hj => ⟨?_, (gen hj).1⟩⟩
  rw [sg_eq, getElem!_pos _ j (by simpa using hj)]
  simp

theorem sE_all (k : Nat) (hk : k < 16) : sEBlk k = true := by
  interval_cases k
  exacts [sEBlk0, sEBlk1, sEBlk2, sEBlk3, sEBlk4, sEBlk5, sEBlk6, sEBlk7, sEBlk8, sEBlk9,
    sEBlk10, sEBlk11, sEBlk12, sEBlk13, sEBlk14, sEBlk15]

theorem cen_all (k : Nat) (hk : k < 16) : cenBlk k = true := by
  interval_cases k
  exacts [cenBlk0, cenBlk1, cenBlk2, cenBlk3, cenBlk4, cenBlk5, cenBlk6, cenBlk7, cenBlk8,
    cenBlk9, cenBlk10, cenBlk11, cenBlk12, cenBlk13, cenBlk14, cenBlk15]

theorem s_pe : ∀ i < J3XS.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true J3XS.G J3XS.GI 8
    J3XS.cnt J3XS.T J3XS.PL J3XS.POS J3XS.SRT J3XS.SRI i = true := by
  intro i hi
  rw [hcnt] at hi
  exact penumSl_spec (sE_all (i / 16) (by omega)) i (by omega) (by omega) (by rw [hcnt]; exact hi)

theorem s_hs : ∀ i < J3XS.cnt,
    hsortPtK 6156 13 (mask 13) J3XS.cnt J3XS.T J3XS.HS J3XS.HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq 6156 13 J3XS.cnt J3XS.T J3XS.HS J3XS.HSI i]
  exact slK_spec sHF i (Nat.zero_le _) (by omega) hi

theorem row (i : Nat) (hi : i < 256) : cenRow i = true := by
  have h := cen_all (i / 16) (by omega)
  unfold cenBlk at h
  have h2 := List.all_eq_true.1 h (i % 16) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  rwa [Nat.div_add_mod] at h2

theorem closure_eq :
    (mulClosureH 6156 sylXGens 256).1 = (hRec 6156 13 J3XS.cnt J3XS.T J3XS.PL).1 := by
  rw [(mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2.2.2 s_pe s_hs).1]

@[expose] noncomputable def fE (i : Nat) : Table := tabT (unpack 6156 13 (J3XS.T i))

theorem syl_eq : sylXList = ((List.range 256).map fE).toArray := by
  unfold sylXList
  rw [closure_eq]
  apply Array.toList_inj.1
  simp only [hRec, Array.toList_ofFn, List.toList_toArray]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, hcnt]
  rfl

theorem hT {i : Nat} (hi : i < 256) : canonK 6156 13 (mask 13) (6156 * 13) (J3XS.T i) = true :=
  penumPt_canon (s_pe i (by rw [hcnt]; exact hi))

theorem t0_eq : t0 = tabT (unpack 6156 13 (J3CentP 9)) := tbl_unpack (by norm_num)

theorem facts25510 : j3OuterCheck = true := by
  unfold j3OuterCheck
  rw [syl_eq, sg_eq, t0_eq]
  simp only [List.any_toArray, List.all_toArray, List.any_map, List.all_map, Function.comp]
  have h9 := base.2.2.2.1
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine (any_mem fun i hi => ?_).trans t0_mem
    simp only [Function.comp_apply, fE]
    rw [tblEq_unpack (hT (List.mem_range.1 hi)) h9]
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have hr := row i hi'
    unfold cenRow commAll at hr
    simp only [Function.comp_apply, fE]
    rw [tblEq_unpack (hT hi') h9, hid, tblEq_unpack (hT hi') hidc]
    refine (congrArg (fun b => !b || Nat.beq (J3XS.T i) (pidn 6156 13) ||
      Nat.beq (J3XS.T i) (J3CentP 9)) (all_mem fun j hj => ?_)).trans hr
    simp only [Function.comp_apply]
    rw [commTT_unpack (hT hi') (gen (List.mem_range.1 hj)).1]
    rfl
  · obtain ⟨i, hi, he⟩ := List.any_eq_true.1 x_mem
    have hi' := List.mem_range.1 hi
    have hx : J3XS.T i = xW := Nat.eq_of_beq_eq_true he
    refine List.any_eq_true.2 ⟨i, hi, ?_⟩
    simp only [Function.comp_apply, fE, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [compT_unpack (hT hi') (hT hi'), compT_unpack (canonK_pcomp (hT hi') (hT hi'))
        (canonK_pcomp (hT hi') (hT hi')),
        tblEq_unpack (canonK_pcomp (canonK_pcomp (hT hi') (hT hi'))
          (canonK_pcomp (hT hi') (hT hi'))) h9, hx]
      exact x_four
    · unfold j3Sift
      rw [natArr_tabT (hT hi'), hx]
      exact CertificateChecks.KernelSporSch.J3KT.sift_of x_word

end CertificateChecks.KernelSpor.J3OutSyl

end
