module

public import Certificates.Kernel.Sporadic.OddCore.J3OutSyl
public import Certificates.Kernel.Sporadic.OddCore.J3HypSylF
public import Certificates.Kernel.SporSch.J3K426.Sift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ3Check
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

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

theorem ntX_spec : ∀ r < 8, ∀ i < 2 ^ r, pcTK 6156 13 (mask 13) J3XS.T J3XcP r i = true := by
  intro r hr i hi
  have key : ∀ k, ntX r k = true → 32 * k ≤ i → i < 32 * k + 32 →
      pcTK 6156 13 (mask 13) J3XS.T J3XcP r i = true := fun k h h1 h2 =>
    slK_spec h i h1 h2 (by rw [shl_one]; exact hi)
  by_cases h5 : r < 5
  · have h16 : 2 ^ r ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact key 0 (CFSG.KS.Raw.Orb.allN_iff.1 ntX_lo r h5) (by omega) (by omega)
  · have hi' := hi
    interval_cases r <;> norm_num at hi'
    · exact key 0 ntX_5 (by omega) (by omega)
    · by_cases h32 : i < 32
      · exact key 0 ntX_60 (by omega) (by omega)
      · exact key 1 ntX_61 (by omega) (by omega)
    · by_cases h32 : i < 32
      · exact key 0 ntX_70 (by omega) (by omega)
      · by_cases h64 : i < 64
        · exact key 1 ntX_71 (by omega) (by omega)
        · by_cases h96 : i < 96
          · exact key 2 ntX_72 (by omega) (by omega)
          · exact key 3 ntX_73 (by omega) (by omega)

theorem rlX_ok {r c : Nat} (hr : r < 8) (hc : 4 * c < max r 1) : rlX r c = true := by
  have hc2 : c < 2 := by omega
  by_cases h5 : r < 5
  · have e : c = 0 := by omega
    rw [e]
    exact CFSG.KS.Raw.Orb.allN_iff.1 rlX_lo r h5
  · interval_cases r <;> interval_cases c
    exacts [rlX_50, rlX_51, rlX_60, rlX_61, rlX_70, rlX_71]

theorem rlX_spec {r : Nat} (hr : r < 8) :
    canonK 6156 13 (mask 13) (6156 * 13) (pcNK J3XS.T J3XcP (2 ^ r)) = true ∧
      (∃ a < 2 ^ r, pcomp 6156 13 (mask 13) (pcNK J3XS.T J3XcP (2 ^ r))
        (pcNK J3XS.T J3XcP (2 ^ r)) = pcNK J3XS.T J3XcP a) ∧
      ∀ s < r, ∃ b < 2 ^ r,
        pcomp 6156 13 (mask 13) (pcNK J3XS.T J3XcP (2 ^ r)) (pcNK J3XS.T J3XcP (2 ^ s)) =
          pcomp 6156 13 (mask 13) (pcNK J3XS.T J3XcP b) (pcNK J3XS.T J3XcP (2 ^ r)) :=
  pcR_spec (rlX_ok (c := 0) hr (by omega)) (fun s hs => rlX_ok (c := s / 4) hr (by omega))

theorem closJ3X : ∀ i < J3XS.cnt, ∀ i' < J3XS.cnt, ∃ q < J3XS.cnt,
    pcomp 6156 13 (mask 13) (pcNK J3XS.T J3XcP i) (pcNK J3XS.T J3XcP i') =
      pcNK J3XS.T J3XcP q := by
  obtain ⟨h0, hc0, -, -⟩ := pcM_spec mbX_ok
  have H := (pc_closed (m := 8) (N := pcNK J3XS.T J3XcP) h0 hc0
    (fun r hr => (rlX_spec hr).1)
    (fun r hr i hi => pcT_spec (ntX_spec r hr i hi))
    (fun r hr => (rlX_spec hr).2.1)
    (fun r hr => (rlX_spec hr).2.2) 8 (Nat.le_refl _)).2
  have e : (2 : Nat) ^ 8 = 256 := by norm_num
  rw [e] at H
  rw [hcnt]
  exact H

theorem s_pe : ∀ i < J3XS.cnt, penumPtK 6156 13 (mask 13) (6156 * 13) true J3XS.G J3XS.GI 8
    J3XS.cnt J3XS.T J3XS.PL J3XS.POS J3XS.SRT J3XS.SRI i = true := by
  have hd := base.2.2.2.2.2.2
  unfold penumHdK at hd
  simp only [bAnd_iff] at hd
  have h0 : canonK 6156 13 (mask 13) (6156 * 13) (J3XS.T 0) = true := by
    rw [Nat.eq_of_beq_eq_true hd.2.2.1]
    exact base.2.1
  have hcl : ∀ c < J3XS.cnt * 8, findPtK J3XS.cnt J3XS.T
      (prodQK 6156 13 (mask 13) 8 J3XS.T J3XS.GI) J3XS.POS c = true := fun c hc =>
    J3HypSyl.pcF_find3 (by norm_num) (by norm_num) closJ3X mbX_ok
      (slK_spec clJ3X c (Nat.zero_le _) (by rw [hcnt] at hc; omega) hc) hc
  exact CFSG.KS.PEnumC.penumPtK_of_C (K := 8) (S := J3XS.GI) (CL := J3XS.POS) (Nat.le_refl _)
    (fun j hj => (gen hj).2.2) (fun _ _ => rfl) (fun j hj => (gen hj).1) h0 hcl
    (fun i hi => slK_spec peX i (Nat.zero_le _) (by rw [hcnt] at hi; omega) hi)

theorem s_hs : ∀ i < J3XS.cnt,
    hsortPtK 6156 13 (mask 13) J3XS.cnt J3XS.T J3XS.HS J3XS.HSI i = true := fun i hi => by
  rw [← hsortPtKF_eq 6156 13 J3XS.cnt J3XS.T J3XS.HS J3XS.HSI i]
  exact slK_spec sHF i (Nat.zero_le _) (by omega) hi

theorem row (i : Nat) (hi : i < 256) : cenRow i = true := by
  have hc := List.all_eq_true.1 center_wK i (List.mem_range.2 hi)
  unfold centerWK at hc
  unfold cenRow commAll
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc ⊢
  rcases hc with (h | h) | ⟨⟨hj, hne⟩, hp⟩
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · rw [Nat.blt_eq] at hj hp
    refine Or.inl (Or.inl (List.all_eq_false.2 ⟨cWJ i, List.mem_range.2 hj, fun he => ?_⟩))
    have hx := congrArg (fun q => pg 13 (mask 13) q (cWP i)) (Nat.eq_of_beq_eq_true he)
    simp only [pc] at hx
    rw [PF.pg_pcomp (n := 6156) (by norm_num) hp, PF.pg_pcomp (n := 6156) (by norm_num) hp] at hx
    exact Nat.ne_of_beq_eq_false hne hx

theorem closure_eq :
    (mulClosureH 6156 sylXGens 256).1 = (hRec 6156 13 J3XS.cnt J3XS.T J3XS.PL).1 := by
  rw [(mulH_sound base.1 (fun j hj => (gen hj).2.2) s_tabs base.2.2.2.2.2.2 s_pe s_hs).1]

@[expose] noncomputable def fE (i : Nat) : Table := tabT (unpack 6156 13 (J3XS.T i))

theorem syl_eq : sylXList = ((List.range 256).map fE).toArray := by
  rw [sylXList_fst, closure_eq]
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
  simp only [List.any_toArray, List.all_toArray, List.any_map, List.all_map]
  have h9 := base.2.2.2.1
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine (any_mem fun i hi => ?_).trans t0_mem
    rw [Function.comp_apply]
    beta_reduce
    rw [fE, tblEq_unpack (hT (List.mem_range.1 hi)) h9]
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have hr := row i hi'
    unfold cenRow commAll at hr
    rw [Function.comp_apply]
    beta_reduce
    rw [fE, tblEq_unpack (hT hi') h9, hid, tblEq_unpack (hT hi') hidc]
    refine (congrArg (fun b => !b || Nat.beq (J3XS.T i) (pidn 6156 13) ||
      Nat.beq (J3XS.T i) (J3CentP 9)) (all_mem fun j hj => ?_)).trans hr
    rw [Function.comp_apply]
    beta_reduce
    rw [commTT_unpack (hT hi') (gen (List.mem_range.1 hj)).1, pc, pc]
  · obtain ⟨i, hi, he⟩ := List.any_eq_true.1 x_mem
    have hi' := List.mem_range.1 hi
    have hx : J3XS.T i = xW := Nat.eq_of_beq_eq_true he
    refine List.any_eq_true.2 ⟨i, hi, ?_⟩
    rw [Function.comp_apply]
    beta_reduce
    rw [fE, Bool.and_eq_true]
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
