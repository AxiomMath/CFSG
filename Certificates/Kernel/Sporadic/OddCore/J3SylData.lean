module

public import Certificates.Kernel.Sporadic.OddCore.J3SylMem
public import Certificates.Kernel.Sporadic.OddCore.J3SylFourPF
public import Certificates.Kernel.Sporadic.OddCore.J3SylFourRF
public import Certificates.Kernel.Sporadic.OddCore.J3SylFourR1F
public import Certificates.Kernel.Sporadic.OddCore.J3OutSylF
public import Certificates.Kernel.Sporadic.OddCore.S16J3Sift27810
public import CFSG.Certificates.Kernel.Spor.ClosedHSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Misc.RuInvHash

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3SylData

open CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.J3
open CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.J3SylMem
open CFSG.KC.BfsPin (canonK_pcomp)
open CFSG.EvenSporadicStandard.Fin76b.J3 (sylXGens)

local notation "⟪" x "⟫" => tabT (unpack 6156 13 x)

abbrev Cn (X : Nat) : Prop := canonK 6156 13 (mask 13) (6156 * 13) X = true

theorem hsz : szOK 6156 13 = true := J3HypSyl.base.1

theorem hidc : Cn (pidn 6156 13) := J3HypSyl.base.2.1

theorem hyp_inv {k : Nat} (hk : k < 12) :
    invEqK 6156 13 (mask 13) (6156 * 13) (J3HypP k) (J3HypI k) = true :=
  allN_spec hypInv k hk

theorem cent_inv {k : Nat} (hk : k < 31) :
    invEqK 6156 13 (mask 13) (6156 * 13) (J3CentP k) (J3CentI k) = true :=
  j3_perm hk

theorem hyp_c {k : Nat} (hk : k < 12) : Cn (J3HypP k) := (canonK_of_invEqK hsz (hyp_inv hk)).1

theorem cent_c {k : Nat} (hk : k < 31) : Cn (J3CentP k) := (canonK_of_invEqK hsz (cent_inv hk)).1

theorem sift_of_word {X : Nat} {wd : List Int} (hX : Cn X) (h : SqrtK26102.j3W wd X = true) :
    j3Sift ⟪X⟫ = true := by
  unfold j3Sift
  rw [natArr_tabT hX, CertificateChecks.KernelSporSch.J3KT.sift_of h]

theorem u_eq : j3OuterTbl = ⟪J3CentP 0⟫ := by
  rw [j3OuterTbl, tbl_unpack (by norm_num)]

theorem sift_u {X : Nat} {wd : List Int} (hX : Cn X) (h : wu wd X = true) :
    j3Sift (compT 6156 ⟪X⟫ j3OuterTbl) = true := by
  rw [u_eq, compT_unpack hX (cent_c (by norm_num))]
  exact sift_of_word (canonK_pcomp hX (cent_c (by norm_num))) h

theorem row_of {X XI : Nat} (hi : invEqK 6156 13 (mask 13) (6156 * 13) X XI = true)
    {memK : Table → Bool} (hm : memK ⟪X⟫ = true) :
    (permOK 6156 ⟪X⟫ && invOK 6156 ⟪X⟫ (invT 6156 ⟪X⟫) && memK ⟪X⟫) = true := by
  have hc := canonK_of_invEqK hsz hi
  rw [invT_unpack (by norm_num) hi, permOK_unpack hc.1 hi, invOK_unpack hc.1 hc.2 hi, hm]
  rfl

theorem memP_of {X t : Nat} {wd : List Int} (hX : Cn X) (ht : Cn t)
    (hs : SqrtK26102.j3W wd X = true) (hc : cm X t = true) : memP ⟪t⟫ ⟪X⟫ = true := by
  unfold memP
  rw [sift_of_word hX hs, commTT_unpack hX ht]
  exact hc

theorem memR_in {X t : Nat} {wd : List Int} (hX : Cn X) (ht : Cn t)
    (hs : SqrtK26102.j3W wd X = true) (hc : cm X t = true) : memR ⟪t⟫ ⟪X⟫ = true := by
  unfold memR
  rw [sift_of_word hX hs, Bool.true_or, commTT_unpack hX ht]
  exact hc

theorem memR_out {X t : Nat} {wd : List Int} (hX : Cn X) (ht : Cn t)
    (hs : wu wd X = true) (hc : cm X t = true) : memR ⟪t⟫ ⟪X⟫ = true := by
  unfold memR
  rw [sift_u hX hs, Bool.or_true, commTT_unpack hX ht]
  exact hc

theorem reps_of {n : Nat} {sg : Array Table} {memK : Table → Bool}
    (h : sg.all (fun x => permOK n x && invOK n x (invT n x) && memK x) = true) :
    ∀ j < sg.size, Rep n sg[j]! (tp n sg[j]!) ∧ Rep n (invT n sg[j]!) (tp n sg[j]!)⁻¹ := by
  intro j hj
  have h1 := (Array.all_eq_true.1 h) j hj
  simp only [Bool.and_eq_true] at h1
  rw [getElem!_pos sg j hj]
  exact ⟨rep_tp h1.1.1, rep_invT (rep_tp h1.1.1) h1.1.2⟩

theorem t0_eq : t0 = ⟪J3CentP 9⟫ := tbl_unpack (by norm_num)

theorem t1_eq : t1 = ⟪J3CentP 21⟫ := tbl_unpack (by norm_num)

theorem c_t0' : allN 14 (fun k => cm (J3CentP (Nat.add k 1)) (J3CentP 9)) = true ∧
    allN 4 (fun k => cm (J3HypP k) (J3CentP 9)) = true :=
  (bAnd_iff _ _).1 c_t0

theorem c_t1' : allN 4 (fun k => cm (J3CentP (Nat.add k 21)) (J3CentP 21)) = true ∧
    allN 4 (fun k => cm (J3HypP (Nat.add k 4)) (J3CentP 21)) = true :=
  (bAnd_iff _ _).1 c_t1

theorem ct0 {k : Nat} (hk : k < 14) : cm (J3CentP (k + 1)) (J3CentP 9) = true :=
  allN_spec c_t0'.1 k hk

theorem ch0 {k : Nat} (hk : k < 4) : cm (J3HypP k) (J3CentP 9) = true :=
  allN_spec c_t0'.2 k hk

theorem ct1 {k : Nat} (hk : k < 4) : cm (J3CentP (k + 21)) (J3CentP 21) = true :=
  allN_spec c_t1'.1 k hk

theorem ch1 {k : Nat} (hk : k < 4) : cm (J3HypP (k + 4)) (J3CentP 21) = true :=
  allN_spec c_t1'.2 k hk

theorem c9 : Cn (J3CentP 9) := cent_c (by norm_num)

theorem c21 : Cn (J3CentP 21) := cent_c (by norm_num)

theorem cRow {k : Nat} (hk : k < 31) {memK : Table → Bool} (hm : memK ⟪J3CentP k⟫ = true) :
    (permOK 6156 (j3CentTbl k) && invOK 6156 (j3CentTbl k) (invT 6156 (j3CentTbl k)) &&
      memK (j3CentTbl k)) = true := by
  rw [tbl_unpack hk]
  exact row_of (cent_inv hk) hm

theorem hRow {k : Nat} (hk : k < 12) {memK : Table → Bool} (hm : memK ⟪J3HypP k⟫ = true) :
    (permOK 6156 (hypTbl k) && invOK 6156 (hypTbl k) (invT 6156 (hypTbl k)) &&
      memK (hypTbl k)) = true := by
  rw [J3HypSyl.hyp_tab hk]
  exact row_of (hyp_inv hk) hm

theorem size_rec {cnt m : Nat} {T PL : Nat → Nat} (hc : cnt = m) :
    ((hRec 6156 13 cnt T PL).1.size == m) = true := by
  simp [hRec, hc]

theorem p0_cg : cgP0.all (fun x => permOK 6156 x && invOK 6156 x (invT 6156 x) && memP t0 x) =
    true := by
  rw [t0_eq, cgP0, List.all_toArray, List.all_eq_true]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact cRow (by norm_num)
      (memP_of (cent_c (by norm_num)) c9 s_cent10 (ct0 (k := 9) (by norm_num)))
  · exact cRow (by norm_num)
      (memP_of (cent_c (by norm_num)) c9 s_cent11 (ct0 (k := 10) (by norm_num)))
  · exact cRow (by norm_num)
      (memP_of (cent_c (by norm_num)) c9 s_cent12 (ct0 (k := 11) (by norm_num)))
  · exact cRow (by norm_num)
      (memP_of (cent_c (by norm_num)) c9 s_cent13 (ct0 (k := 12) (by norm_num)))
  · exact cRow (by norm_num)
      (memP_of (cent_c (by norm_num)) c9 s_cent14 (ct0 (k := 13) (by norm_num)))

theorem p0_sg : sgP0.all (fun x => permOK 6156 x && invOK 6156 x (invT 6156 x) && memP t0 x) =
    true := by
  rw [t0_eq, sgP0, List.all_toArray, List.all_eq_true]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact hRow (by norm_num)
      (memP_of (hyp_c (by norm_num)) c9 s_hyp1 (ch0 (k := 1) (by norm_num)))
  · exact hRow (by norm_num)
      (memP_of (hyp_c (by norm_num)) c9 s_hyp2 (ch0 (k := 2) (by norm_num)))
  · exact hRow (by norm_num)
      (memP_of (hyp_c (by norm_num)) c9 s_hyp3 (ch0 (k := 3) (by norm_num)))

theorem p0_ok : sylowFourOK 6156 128 6 (memP t0) cgP0 sgP0 128 = true := by
  have M := mulH_sound J3HypSyl.base.1 (fun j hj => (J3HypSyl.gen hj).2.2) J3HypSyl.s_tabs
    J3HypSyl.base.2.2.2.2.2.2 J3HypSyl.s_pe J3HypSyl.s_hs
  have hcl := closedOKH_of_mulH J3HypSyl.base.1 (fun j hj => (J3HypSyl.gen hj).2.2)
    J3HypSyl.s_tabs (reps_of p0_sg) J3HypSyl.base.2.2.2.2.2.2 J3HypSyl.s_pe J3HypSyl.s_hs
  have hr := J3SylFourP.p0_rows
  rw [M.1] at hr
  unfold sylowFourOK
  simp only [M.1, p0_cg, p0_sg, M.2.1, hcl, M.2.2, hr, size_rec J3HypSyl.hcnt, Bool.and_self]

theorem z0_row : (permOK 6156 z0 && invOK 6156 z0 (invT 6156 z0) && memR t0 z0) = true := by
  rw [t0_eq, z0]
  exact hRow (by norm_num) (memR_out (hyp_c (by norm_num)) c9 s_hyp0 (ch0 (k := 0) (by norm_num)))

theorem r0_cg : cgR0.all (fun x => permOK 6156 x && invOK 6156 x (invT 6156 x) && memR t0 x) =
    true := by
  have hz := z0_row
  rw [t0_eq] at hz ⊢
  rw [cgR0, List.all_toArray, List.all_eq_true]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c9 s_cent10 (ct0 (k := 9) (by norm_num)))
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c9 s_cent11 (ct0 (k := 10) (by norm_num)))
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c9 s_cent12 (ct0 (k := 11) (by norm_num)))
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c9 s_cent13 (ct0 (k := 12) (by norm_num)))
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c9 s_cent14 (ct0 (k := 13) (by norm_num)))
  · exact hz

theorem r0_gen {k : Nat} (hk : k < 8) :
    memR ⟪J3CentP 9⟫ ⟪J3CentP (k + 1)⟫ = true := by
  have hc := ct0 (k := k) (by omega)
  have hX : Cn (J3CentP (k + 1)) := cent_c (by omega)
  interval_cases k
  · exact memR_in hX c9 s_cent1 hc
  · exact memR_in hX c9 s_cent2 hc
  · exact memR_in hX c9 s_cent3 hc
  · exact memR_out hX c9 s_cent4 hc
  · exact memR_in hX c9 s_cent5 hc
  · exact memR_in hX c9 s_cent6 hc
  · exact memR_out hX c9 s_cent7 hc
  · exact memR_in hX c9 s_cent8 hc

theorem r0_sg : j3SylowGenTbls.toArray.all
    (fun x => permOK 6156 x && invOK 6156 x (invT 6156 x) && memR t0 x) = true := by
  rw [t0_eq, j3SylowGenTbls, List.all_toArray, List.all_map, List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  exact cRow (by omega) (r0_gen hk')

theorem r0_ok : sylowFourOK 6156 256 6 (memR t0) cgR0 j3SylowGenTbls.toArray 256 = true := by
  have M := mulH_sound J3OutSyl.base.1 (fun j hj => (J3OutSyl.gen hj).2.2) J3OutSyl.s_tabs
    J3OutSyl.base.2.2.2.2.2.2 J3OutSyl.s_pe J3OutSyl.s_hs
  have hcl := closedOKH_of_mulH J3OutSyl.base.1 (fun j hj => (J3OutSyl.gen hj).2.2)
    J3OutSyl.s_tabs (reps_of r0_sg) J3OutSyl.base.2.2.2.2.2.2 J3OutSyl.s_pe J3OutSyl.s_hs
  have hr := J3SylFourR.r0_rows
  change (mulClosureH 6156 sylXGens 256).1.all _ = true at hr
  rw [M.1] at hr
  unfold sylowFourOK
  change (_ && _ && mulTreeOK 6156 sylXGens (mulClosureH 6156 sylXGens 256).1
    (mulClosureH 6156 sylXGens 256).2.1 (mulClosureH 6156 sylXGens 256).2.2 &&
    closedOKH 6156 (sylXGens ++ sylXGens.map (invT 6156)) (mulClosureH 6156 sylXGens 256).1 &&
    hkeysDistinct 6156 (mulClosureH 6156 sylXGens 256).1.toList &&
    ((mulClosureH 6156 sylXGens 256).1.size == 256) &&
    (mulClosureH 6156 sylXGens 256).1.all _) = true
  simp only [M.1, r0_cg, r0_sg, M.2.1, hcl, M.2.2, hr, size_rec J3OutSyl.hcnt, Bool.and_self]

theorem r1_cg : cgR1.all (fun x => permOK 6156 x && invOK 6156 x (invT 6156 x) && memR t1 x) =
    true := by
  rw [t1_eq, cgR1, t1_eq, List.all_toArray, List.all_eq_true]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c21 s_cent22 (ct1 (k := 1) (by norm_num)))
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c21 s_cent23 (ct1 (k := 2) (by norm_num)))
  · exact cRow (by norm_num)
      (memR_in (cent_c (by norm_num)) c21 s_cent24 (ct1 (k := 3) (by norm_num)))
  · exact row_of (cent_inv (by norm_num))
      (memR_out (cent_c (by norm_num)) c21 s_cent21 (ct1 (k := 0) (by norm_num)))

theorem r1_sg : sgR1.all (fun x => permOK 6156 x && invOK 6156 x (invT 6156 x) && memR t1 x) =
    true := by
  rw [t1_eq, sgR1, List.all_toArray, List.all_eq_true]
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hRow (by norm_num)
      (memR_in (hyp_c (by norm_num)) c21 s_hyp4 (ch1 (k := 0) (by norm_num)))
  · exact hRow (by norm_num)
      (memR_out (hyp_c (by norm_num)) c21 s_hyp5 (ch1 (k := 1) (by norm_num)))
  · exact hRow (by norm_num)
      (memR_out (hyp_c (by norm_num)) c21 s_hyp6 (ch1 (k := 2) (by norm_num)))
  · exact hRow (by norm_num)
      (memR_in (hyp_c (by norm_num)) c21 s_hyp7 (ch1 (k := 3) (by norm_num)))

theorem r1_ok : sylowFourOK 6156 32 6 (memR t1) cgR1 sgR1 32 = true := by
  have M := J3SylFourR1.r1_mul
  have hcl := closedOKH_of_mulH J3SylFourR1.base.1 (fun j hj => (J3SylFourR1.gen hj).2.2)
    J3SylFourR1.s_tabs (reps_of r1_sg) J3SylFourR1.base.2.2.2.2 J3SylFourR1.s_pe J3SylFourR1.s_hs
  have hr := J3SylFourR1.r1_rows
  rw [M.1] at hr
  unfold sylowFourOK
  simp only [M.1, r1_cg, r1_sg, M.2.1, hcl, M.2.2, hr, size_rec J3SylFourR1.hcnt, Bool.and_self]

section Out


theorem out_of {X XI : Nat} {iw : List Int} (hi : invEqK 6156 13 (mask 13) (6156 * 13) X XI = true)
    (h : S16J3.outJ3 iw X = true) : j3Sift ⟪X⟫ = false :=
  S16J3.sift_false_of_out (canonK_of_invEqK hsz hi).1 hi h

theorem z_ok {X XI t : Nat} {iw wd : List Int}
    (hi : invEqK 6156 13 (mask 13) (6156 * 13) X XI = true) (ht : Cn t)
    (ho : S16J3.outJ3 iw X = true) (hs : wu wd X = true) (hc : cm X t = true) :
    zOK 6156 j3Sift j3OuterTbl ⟪t⟫ ⟪X⟫ = true := by
  have hX := (canonK_of_invEqK hsz hi).1
  unfold zOK
  rw [permOK_unpack hX hi, out_of hi ho, sift_u hX hs, commTT_unpack hX ht, Bool.or_true]
  exact hc

theorem perm_cent {k : Nat} (hk : k < 31) : permOK 6156 (j3CentTbl k) = true := by
  rw [tbl_unpack hk]
  exact permOK_unpack (cent_c hk) (cent_inv hk)

theorem sylowData_ok : sylowData = true := by
  unfold sylowData
  have hz0 : zOK 6156 j3Sift j3OuterTbl t0 z0 = true := by
    rw [t0_eq, z0, J3HypSyl.hyp_tab (by norm_num)]
    exact z_ok (hyp_inv (by norm_num)) c9 o_z0 s_hyp0 (ch0 (k := 0) (by norm_num))
  have ht1 : zOK 6156 j3Sift j3OuterTbl t1 t1 = true := by
    rw [t1_eq]
    exact z_ok (cent_inv (by norm_num)) c21 o_t1 s_cent21 (ct1 (k := 0) (by norm_num))
  rw [j3OuterTbl] at hz0 ht1 ⊢
  rw [perm_cent (by norm_num), perm_cent (k := 9) (by norm_num), perm_cent (k := 21) (by norm_num),
    p0_ok, r0_ok, r1_ok, hz0, ht1]
  rfl

end Out

theorem divParts_two : CFSG.Sporadic.Schreier.Native.divParts 2 = [1] := by decide

theorem ord2 {X : Nat} (hX : Cn X) : ordTest 6156 2 ⟪X⟫ = invo X := by
  have hP : CFSG.KS.MulH.Pows 6156 13 X
      (fun e => Nat.rec (motive := fun _ => Nat) (pidn 6156 13)
        (fun _ acc => pcomp 6156 13 (mask 13) X acc) e) := ⟨rfl, fun _ => rfl⟩
  rw [ordTest_unpack hP (CFSG.KC.BfsPin.idA_eq hsz) hidc hX 2, divParts_two]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  change (Nat.beq (pcomp 6156 13 (mask 13) X (pcomp 6156 13 (mask 13) X (pidn 6156 13)))
      (pidn 6156 13) && !Nat.beq (pcomp 6156 13 (mask 13) X (pidn 6156 13)) (pidn 6156 13)) =
    invo X
  rw [pcomp_idR' hX]
  unfold invo S16J3.pc
  cases Nat.beq (pcomp 6156 13 (mask 13) X X) (pidn 6156 13) <;>
    cases Nat.beq X (pidn 6156 13) <;> rfl

theorem commT_unpack {p q : Nat} (hp : Cn p) (hq : Cn q) :
    commT 6156 ⟪p⟫ ⟪q⟫ = cm p q := by
  unfold commT
  rw [compT_unpack hp hq, compT_unpack hq hp,
    tblEq_unpack (canonK_pcomp hp hq) (canonK_pcomp hq hp)]
  rfl

theorem e8_data : e8Data = true := by
  have ha := hyp_c (k := 8) (by norm_num)
  have hb := hyp_c (k := 9) (by norm_num)
  have hc := hyp_c (k := 10) (by norm_num)
  have h := e8_ok
  unfold e8K at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold e8Data e8Rows e8Check
  rw [J3HypSyl.hyp_tab (by norm_num), J3HypSyl.hyp_tab (by norm_num),
    J3HypSyl.hyp_tab (by norm_num), permOK_unpack ha (hyp_inv (by norm_num)),
    permOK_unpack hb (hyp_inv (by norm_num)), permOK_unpack hc (hyp_inv (by norm_num)),
    sift_of_word ha s_hyp8, sift_of_word hb s_hyp9, sift_of_word hc s_hyp10,
    commT_unpack ha hb, commT_unpack ha hc, commT_unpack hb hc, ord2 ha, ord2 hb, ord2 hc,
    compT_unpack ha hb, compT_unpack ha hc, compT_unpack hb hc,
    compT_unpack (canonK_pcomp ha hb) hc, ord2 (canonK_pcomp ha hb), ord2 (canonK_pcomp ha hc),
    ord2 (canonK_pcomp hb hc), ord2 (canonK_pcomp (canonK_pcomp ha hb) hc)]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  rfl

theorem fours_data : foursData = true := by
  have hl := hyp_c (k := 11) (by norm_num)
  have hli := (canonK_of_invEqK hsz (hyp_inv (k := 11) (by norm_num))).2
  have hti := (canonK_of_invEqK hsz (cent_inv (k := 21) (by norm_num))).2
  unfold foursData foursWitOK commTable
  rw [J3HypSyl.hyp_tab (by norm_num), t1_eq, invT_unpack (by norm_num) (hyp_inv (by norm_num)),
    invT_unpack (by norm_num) (cent_inv (by norm_num)),
    permOK_unpack hl (hyp_inv (by norm_num)), sift_of_word hl s_hyp11,
    invOK_unpack hl hli (hyp_inv (by norm_num)), permOK_unpack c21 (cent_inv (by norm_num)),
    invOK_unpack c21 hti (cent_inv (by norm_num)), compT_unpack hl c21,
    compT_unpack (canonK_pcomp hl c21) hli,
    compT_unpack (canonK_pcomp (canonK_pcomp hl c21) hli) hti,
    ord2 (canonK_pcomp (canonK_pcomp (canonK_pcomp hl c21) hli) hti)]
  exact J3SylMem.four_ok

theorem facts24431 :
    sylowData = true ∧ e8Data = true ∧ foursData = true :=
  ⟨sylowData_ok, e8_data, fours_data⟩

end CertificateChecks.KernelSpor.J3SylData

end
