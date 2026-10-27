module

public import Certificates.Kernel.J3Ref.EnumFacts
public import Certificates.Kernel.J3Ref.Perm
import CFSG.Certificates.Kernel.J2ModelsSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ3Ref

open CFSG.SectionRank.QTK.Insp443.J3Cls CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.PEnumB
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem tbP_cls {k : Nat} (hk : k < 10) : tbP (k + 1) = J3ClsP k := by
  have h1 : Nat.beq (k + 1) 0 = false := by
    cases e : Nat.beq (k + 1) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
  have h2 : Nat.blt (k + 1) 11 = true := Nat.blt_eq.mpr (by omega)
  unfold tbP
  rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.nIf_eq, h1, h2]
  simp

theorem tbI_cls {k : Nat} (hk : k < 10) : tbI (k + 1) = J3ClsI k := by
  have h1 : Nat.beq (k + 1) 0 = false := by
    cases e : Nat.beq (k + 1) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
  have h2 : Nat.blt (k + 1) 11 = true := Nat.blt_eq.mpr (by omega)
  unfold tbI
  rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.nIf_eq, h1, h2]
  simp

theorem tbP_cent {k : Nat} (hk : 10 ≤ k) : tbP (k + 1) = J3CentP k := by
  have h1 : Nat.beq (k + 1) 0 = false := by
    cases e : Nat.beq (k + 1) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
  have h2 : Nat.blt (k + 1) 11 = false := by
    cases e : Nat.blt (k + 1) 11
    · rfl
    · exact absurd (Nat.blt_eq.mp e) (by omega)
  unfold tbP
  rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.nIf_eq, h1, h2]
  simp

theorem tbI_cent {k : Nat} (hk : 10 ≤ k) : tbI (k + 1) = J3CentI k := by
  have h1 : Nat.beq (k + 1) 0 = false := by
    cases e : Nat.beq (k + 1) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
  have h2 : Nat.blt (k + 1) 11 = false := by
    cases e : Nat.blt (k + 1) 11
    · rfl
    · exact absurd (Nat.blt_eq.mp e) (by omega)
  unfold tbI
  rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.nIf_eq, h1, h2]
  simp

theorem tbP_zero : tbP 0 = J3CentP 9 := rfl

theorem allTbls_eq : allTbls = (List.range 16).map fun i => tab (tbP i) := by
  simp only [allTbls, eB, omT, scT, mGens, sGens, cGens, List.cons_append, List.nil_append]
  rw [clsTbl_tab (by norm_num), clsTbl_tab (by norm_num), clsTbl_tab (by norm_num),
    clsTbl_tab (by norm_num), clsTbl_tab (by norm_num), clsTbl_tab (by norm_num),
    clsTbl_tab (by norm_num), clsTbl_tab (by norm_num), clsTbl_tab (by norm_num),
    clsTbl_tab (by norm_num), tbl_unpack (by norm_num), tbl_unpack (by norm_num),
    tbl_unpack (by norm_num), tbl_unpack (by norm_num), tbl_unpack (by norm_num),
    tbl_unpack (by norm_num)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append]
  rw [tbP_zero, tbP_cls (k := 0) (by norm_num), tbP_cls (k := 1) (by norm_num),
    tbP_cls (k := 2) (by norm_num), tbP_cls (k := 3) (by norm_num), tbP_cls (k := 4) (by norm_num),
    tbP_cls (k := 5) (by norm_num), tbP_cls (k := 6) (by norm_num), tbP_cls (k := 7) (by norm_num),
    tbP_cls (k := 8) (by norm_num), tbP_cls (k := 9) (by norm_num),
    tbP_cent (k := 10) (by norm_num), tbP_cent (k := 11) (by norm_num),
    tbP_cent (k := 12) (by norm_num), tbP_cent (k := 13) (by norm_num),
    tbP_cent (k := 14) (by norm_num)]

theorem eB_eq : eB = ebL.map tab := by
  simp only [eB, ebL, List.map_cons, List.map_nil]
  rw [clsTbl_tab (by norm_num), clsTbl_tab (by norm_num), clsTbl_tab (by norm_num),
    tbl_unpack (by norm_num)]

theorem hasP_pidn : HasP (pidn 6156 13) 1 :=
  ⟨mj_faith.canon _ mj_faith.id, KernelK426J3.GJ.one_mem, fun x => by
    rw [PF.pg_pidn (by norm_num) (by norm_num) x.2]
    rfl⟩

theorem eb_perms : ∃ Ls : List Pm, List.Forall₂ HasP ebL Ls := by
  obtain ⟨A0, h0⟩ := hasP_of_mj (mj_tbP (i := 0) (by norm_num))
  obtain ⟨A1, h1⟩ := hasP_of_mj (mj_tbP (i := 1) (by norm_num))
  obtain ⟨A2, h2⟩ := hasP_of_mj (mj_tbP (i := 2) (by norm_num))
  obtain ⟨A3, h3⟩ := hasP_of_mj (mj_tbP (i := 3) (by norm_num))
  rw [tbP_zero] at h0
  rw [tbP_cls (k := 0) (by norm_num)] at h1
  rw [tbP_cls (k := 1) (by norm_num)] at h2
  rw [tbP_cls (k := 2) (by norm_num)] at h3
  exact ⟨[A0, A1, A2, A3], .cons h0 (.cons h1 (.cons h2 (.cons h3 .nil)))⟩

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem forall₂_mem_left {L : List Nat} {Ls : List Pm} (hL : List.Forall₂ HasP L Ls) :
    ∀ X ∈ L, ∃ A, HasP X A := by
  induction hL with
  | nil => simp
  | cons hXA _ ih =>
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact ⟨_, hXA⟩
    · exact ih X hX

theorem listRec_all (f : Nat → Bool) (L : List Nat) :
    List.rec (motive := fun _ => Bool) true
      (fun b _ ih => Bool.rec (motive := fun _ => Bool) false ih (f b)) L = L.all f := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    change Bool.rec (motive := fun _ => Bool) false _ (f b) = _
    rw [CFSG.KS.Raw.Orb.bAnd_eq, ih, List.all_cons]

theorem cls_mj {k : Nat} (hk : k < 10) : MJ (J3ClsP k) := by
  rw [← tbP_cls hk]
  exact mj_tbP (by omega)

theorem clsI_mj {k : Nat} (hk : k < 10) : MJ (J3ClsI k) := by
  rw [← tbI_cls hk]
  exact mj_tbI (by omega)

theorem cls_inv {k : Nat} (hk : k < 10) :
    invEqK 6156 13 (mask 13) (6156 * 13) (J3ClsP k) (J3ClsI k) = true := by
  rw [← tbP_cls hk, ← tbI_cls hk]
  exact (tb_facts (by omega)).2.2

theorem cent_mj {k : Nat} (hk : 10 ≤ k) (hk' : k < 15) : MJ (J3CentP k) := by
  rw [← tbP_cent hk]
  exact mj_tbP (by omega)

theorem centI_mj {k : Nat} (hk : 10 ≤ k) (hk' : k < 15) : MJ (J3CentI k) := by
  rw [← tbI_cent hk]
  exact mj_tbI (by omega)

theorem cent_inv {k : Nat} (hk : 10 ≤ k) (hk' : k < 15) :
    invEqK 6156 13 (mask 13) (6156 * 13) (J3CentP k) (J3CentI k) = true := by
  rw [← tbP_cent hk, ← tbI_cent hk]
  exact (tb_facts (by omega)).2.2

theorem head_facts {k cnt m : Nat} {G GI T PL : Nat → Nat} {P : Nat → Nat}
    (h : bAnd(allN k (fun j => bAnd(Nat.beq (GI j) (P j), Nat.beq (G j) (pidn 6156 13))),
      bAnd(Nat.beq cnt m, penumHdK (pidn 6156 13) cnt 3000 T PL)) = true) :
    (∀ j < k, GI j = P j ∧ G j = pidn 6156 13) ∧ cnt = m ∧
      penumHdK (pidn 6156 13) cnt 3000 T PL = true := by
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h2, h3⟩
  have := allN_spec h1 j hj
  simp only [bAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem s_hd : (∀ j < 3, J3RS.GI j = J3ClsP (Nat.add j 7) ∧ J3RS.G j = pidn 6156 13) ∧
    J3RS.cnt = 128 ∧ penumHdK (pidn 6156 13) J3RS.cnt 3000 J3RS.T J3RS.PL = true :=
  head_facts s_head

theorem s_enum : enumOK 6156 3000 128 sGens = true ∧
    mulClosureH 6156 sGens.toArray 3000 = hRec 6156 13 J3RS.cnt J3RS.T J3RS.PL ∧
    ∀ i < J3RS.cnt, MJ (J3RS.T i) := by
  have hGI : ∀ j < 3, J3RS.GI j = J3ClsP (j + 7) := fun j hj => (s_hd.1 j hj).1
  refine enum_of (k := 3) (G := J3RS.G) (GI := J3RS.GI) (GJ := sGJ) (T := J3RS.T) (PL := J3RS.PL)
    (POS := J3RS.POS) (SRT := J3RS.SRT) (SRI := J3RS.SRI) (HS := J3RS.HS) (HSI := J3RS.HSI)
    (HV := J3RSV) (CL := J3RSCl) ⟨by simp [sGens], fun j hj => ?_⟩
    (fun j hj => (s_hd.1 j hj).2) (fun j hj => by rw [hGI j hj]; exact cls_mj (by omega))
    (fun j hj => clsI_mj (k := j + 7) (by omega))
    (fun j hj => by rw [hGI j hj]; exact cls_inv (k := j + 7) (by omega))
    s_hd.2.2 ?_ hvS_all ?_ ?_ s_hd.2.1
  · rw [hGI j hj]
    refine ⟨?_, (cls_mj (by omega)).1⟩
    interval_cases j <;> simp [sGens, clsTbl_tab]
  · rw [s_hd.2.1]
    refine blocks_spec (B := 32) (N := 4) (fun b hb => ?_)
    interval_cases b
    · exact sE0
    · exact sE1
    · exact sE2
    · exact sE3
  · intro i hi
    have := allBlk_spec sHV i (by rw [s_hd.2.1] at hi; exact hi)
    simpa using this
  · intro c hc
    exact bounded_spec (B := 256) (N := 3) (by simp [s_hd.2.1]) sCl_all c
      (by rw [s_hd.2.1] at hc ⊢; simpa using hc)

theorem c_hd : (∀ j < 5, J3RC.GI j = J3CentP (Nat.add j 10) ∧ J3RC.G j = pidn 6156 13) ∧
    J3RC.cnt = 1920 ∧ penumHdK (pidn 6156 13) J3RC.cnt 3000 J3RC.T J3RC.PL = true :=
  head_facts c_head

theorem c_enum : enumOK 6156 3000 1920 cGens = true ∧
    mulClosureH 6156 cGens.toArray 3000 = hRec 6156 13 J3RC.cnt J3RC.T J3RC.PL ∧
    ∀ i < J3RC.cnt, MJ (J3RC.T i) := by
  have hGI : ∀ j < 5, J3RC.GI j = J3CentP (j + 10) := fun j hj => (c_hd.1 j hj).1
  refine enum_of (k := 5) (G := J3RC.G) (GI := J3RC.GI) (GJ := cGJ) (T := J3RC.T) (PL := J3RC.PL)
    (POS := J3RC.POS) (SRT := J3RC.SRT) (SRI := J3RC.SRI) (HS := J3RC.HS) (HSI := J3RC.HSI)
    (HV := J3RCV) (CL := J3RCCl) ⟨by simp [cGens], fun j hj => ?_⟩
    (fun j hj => (c_hd.1 j hj).2) (fun j hj => by rw [hGI j hj]; exact cent_mj (by omega) (by omega))
    (fun j hj => centI_mj (k := j + 10) (by omega) (by omega))
    (fun j hj => by rw [hGI j hj]; exact cent_inv (k := j + 10) (by omega) (by omega))
    c_hd.2.2 ?_ hvC_all ?_ ?_ c_hd.2.1
  · rw [hGI j hj]
    refine ⟨?_, (cent_mj (by omega) (by omega)).1⟩
    interval_cases j <;> simp [cGens, tbl_unpack]
  · rw [c_hd.2.1]
    exact blocks_spec (B := 64) (N := 30) (fun b hb => cPt_all b hb)
  · intro i hi
    rw [c_hd.2.1] at hi
    exact blocks_spec (B := 64) (N := 30) (fun b hb => cHS_all b hb) i hi
  · intro c hc
    exact bounded_spec (B := 640) (N := 30) (by simp [c_hd.2.1]) cCl_all c
      (by rw [c_hd.2.1] at hc ⊢; simpa using hc)

theorem m_hd : (∀ j < 2, J3RM.GI j = J3ClsP (Nat.add j 5) ∧ J3RM.G j = pidn 6156 13) ∧
    J3RM.cnt = 960 ∧ penumHdK (pidn 6156 13) J3RM.cnt 3000 J3RM.T J3RM.PL = true :=
  head_facts m_head

theorem m_enum : enumOK 6156 3000 960 mGens = true ∧
    mulClosureH 6156 mGens.toArray 3000 = hRec 6156 13 J3RM.cnt J3RM.T J3RM.PL ∧
    ∀ i < J3RM.cnt, MJ (J3RM.T i) := by
  have hGI : ∀ j < 2, J3RM.GI j = J3ClsP (j + 5) := fun j hj => (m_hd.1 j hj).1
  refine enum_of (k := 2) (G := J3RM.G) (GI := J3RM.GI) (GJ := mGJ) (T := J3RM.T) (PL := J3RM.PL)
    (POS := J3RM.POS) (SRT := J3RM.SRT) (SRI := J3RM.SRI) (HS := J3RM.HS) (HSI := J3RM.HSI)
    (HV := J3RMV) (CL := J3RMCl) ⟨by simp [mGens], fun j hj => ?_⟩
    (fun j hj => (m_hd.1 j hj).2) (fun j hj => by rw [hGI j hj]; exact cls_mj (by omega))
    (fun j hj => clsI_mj (k := j + 5) (by omega))
    (fun j hj => by rw [hGI j hj]; exact cls_inv (k := j + 5) (by omega))
    m_hd.2.2 ?_ hvM_all ?_ ?_ m_hd.2.1
  · rw [hGI j hj]
    refine ⟨?_, (cls_mj (by omega)).1⟩
    interval_cases j <;> simp [mGens, clsTbl_tab]
  · rw [m_hd.2.1]
    exact blocks_spec (B := 64) (N := 15) (fun b hb => mPt_all b hb)
  · intro i hi
    rw [m_hd.2.1] at hi
    exact blocks_spec (B := 64) (N := 15) (fun b hb => mHS_all b hb) i hi
  · intro c hc
    exact bounded_spec (B := 640) (N := 6) (by simp [m_hd.2.1]) mCl_all c
      (by rw [m_hd.2.1] at hc ⊢; simpa using hc)

theorem n_hd : (∀ j < 3, J3RN.GI j = nGP j ∧ J3RN.G j = pidn 6156 13) ∧
    J3RN.cnt = 2880 ∧ penumHdK (pidn 6156 13) J3RN.cnt 3000 J3RN.T J3RN.PL = true :=
  head_facts n_head

theorem nGP_eq {j : Nat} (hj : j < 3) :
    nGP j = J3ClsP (if j < 2 then j + 5 else 3) ∧ nGJ j = J3ClsI (if j < 2 then j + 5 else 3) := by
  interval_cases j <;> exact ⟨rfl, rfl⟩

theorem n_enum : enumOK 6156 3000 2880 nGens = true ∧
    mulClosureH 6156 nGens.toArray 3000 = hRec 6156 13 J3RN.cnt J3RN.T J3RN.PL ∧
    ∀ i < J3RN.cnt, MJ (J3RN.T i) := by
  have hGI : ∀ j < 3, J3RN.GI j = nGP j := fun j hj => (n_hd.1 j hj).1
  have hk : ∀ j < 3, (if j < 2 then j + 5 else 3) < 10 := fun j hj => by split_ifs <;> omega
  refine enum_of (k := 3) (G := J3RN.G) (GI := J3RN.GI) (GJ := nGJ) (T := J3RN.T) (PL := J3RN.PL)
    (POS := J3RN.POS) (SRT := J3RN.SRT) (SRI := J3RN.SRI) (HS := J3RN.HS) (HSI := J3RN.HSI)
    (HV := J3RNV) (CL := J3RNCl) ⟨by simp [nGens], fun j hj => ?_⟩
    (fun j hj => (n_hd.1 j hj).2)
    (fun j hj => by rw [hGI j hj, (nGP_eq hj).1]; exact cls_mj (hk j hj))
    (fun j hj => by rw [(nGP_eq hj).2]; exact clsI_mj (hk j hj))
    (fun j hj => by rw [hGI j hj, (nGP_eq hj).1, (nGP_eq hj).2]; exact cls_inv (hk j hj))
    n_hd.2.2 ?_ hvN_all ?_ ?_ n_hd.2.1
  · rw [hGI j hj, (nGP_eq hj).1]
    refine ⟨?_, (cls_mj (hk j hj)).1⟩
    interval_cases j <;> simp [nGens, clsTbl_tab]
  · rw [n_hd.2.1]
    exact blocks_spec (B := 64) (N := 45) (fun b hb => nPt_all b hb)
  · intro i hi
    rw [n_hd.2.1] at hi
    exact blocks_spec (B := 64) (N := 45) (fun b hb => nHS_all b hb) i hi
  · intro c hc
    exact bounded_spec (B := 640) (N := 27) (by simp [n_hd.2.1]) nCl_all c
      (by rw [n_hd.2.1] at hc ⊢; simpa using hc)

theorem tbls_true : tblsOK = true := by
  unfold tblsOK
  rw [allTbls_eq, List.all_map, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨hc, -, hinv⟩ := tb_facts hi'
  rw [Function.comp_apply]
  simp only [Bool.and_eq_true]
  refine ⟨permOK_unpack hc hinv, ?_⟩
  unfold j3Sift
  rw [natArr_tabT hc]
  have h := wordOK_all i hi'
  unfold wordOK at h
  exact CertificateChecks.KernelSporSch.J3KT.sift_of h

theorem len_ebL : (ebL.map tab).length = 4 := rfl

theorem eb_true : ebasisOK 6156 eB = true := by
  obtain ⟨Ls, hL⟩ := eb_perms
  have hX := forall₂_mem_left hL
  have h := eb_ok
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold ebasisOK
  rw [eB_eq, len_ebL]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_map, ← h1]
    refine all_congr_mem fun X hXm => ?_
    obtain ⟨A, hA⟩ := hX X hXm
    rw [Function.comp_apply]
    exact tblEq_sq hA
  · rw [List.all_map, ← h2]
    refine all_congr_mem fun X hXm => ?_
    obtain ⟨A, hA⟩ := hX X hXm
    rw [Function.comp_apply, List.all_map]
    refine all_congr_mem fun Y hYm => ?_
    obtain ⟨B, hB⟩ := hX Y hYm
    rw [Function.comp_apply]
    exact commT_eq hA hB
  · rw [CFSG.KS.Raw.Orb.allN_eq] at h3
    rw [show (2 : Nat) ^ 4 = 16 by norm_num, ← h3]
    refine all_congr_mem fun c _ => ?_
    rw [tblEq_eq (rep_maskProd ebL Ls hL c) (Rep.idT (by norm_num)), CFSG.KS.Raw.Orb.bIf_eq,
      spanEqB_eq hL hasP_pidn c]
    by_cases hc : c = 0
    · subst hc
      rfl
    · have e : Nat.beq c 0 = false := by
        cases e : Nat.beq c 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hc
      rw [if_neg (by rw [e]; decide)]
      have e' : (c == 0) = false := by simpa using hc
      rw [e', Bool.false_or]
      congr 1
      exact Bool.eq_iff_iff.2 (by simp [eq_comm])

theorem masks_of {G : Nat} (hG : MJ G) {masks : List Nat} (hlen : masks.length = 4)
    (hk : masksB G masks = true) : masksOK 6156 eB (tab G) masks = true := by
  obtain ⟨Ls, hL⟩ := eb_perms
  have hX := forall₂_mem_left hL
  obtain ⟨Gp, hGp⟩ := hasP_of_mj hG
  unfold masksOK
  rw [eB_eq, len_ebL, hlen]
  simp only [beq_self_eq_true, Bool.true_and]
  unfold masksB at hk
  rw [← hk, List.zip_map_left, List.all_map]
  refine all_congr_mem fun p hp => ?_
  obtain ⟨B, hB⟩ := hX p.1 (List.of_mem_zip hp).1
  rw [Function.comp_apply]
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  rw [tblEq_eq ((rep_tab hGp).compT (rep_tab hB)) ((rep_maskProd ebL Ls hL p.2).compT (rep_tab hGp)),
    spanCompB_eq hL hGp hB hGp p.2]

theorem masks_true : masksOK 6156 eB omT [2, 3, 8, 12] = true ∧
    masksOK 6156 eB (clsTbl 5) [3, 1, 10, 15] = true ∧
    masksOK 6156 eB (clsTbl 6) [10, 15, 3, 1] = true := by
  have h := masks_ok
  simp only [bAnd_iff] at h
  unfold omT
  rw [clsTbl_tab (by norm_num), clsTbl_tab (by norm_num), clsTbl_tab (by norm_num)]
  exact ⟨masks_of (cls_mj (by norm_num)) rfl h.1, masks_of (cls_mj (by norm_num)) rfl h.2.1,
    masks_of (cls_mj (by norm_num)) rfl h.2.2⟩

theorem cent_true : centCount 6156 3000 cGens eB = 16 := by
  obtain ⟨Ls, hL⟩ := eb_perms
  have hX := forall₂_mem_left hL
  unfold centCount
  rw [c_enum.2.1, countP_hRec (hi := 30) (q := fun i => centB 13 (mask 13) bsJ ebL (J3RC.T i))
    (by rw [c_hd.2.1]) (fun i hi => ?_)]
  · exact Nat.eq_of_beq_eq_true c_cent
  · obtain ⟨A, hA⟩ := hasP_of_mj (c_enum.2.2 i hi)
    unfold centB
    rw [listRec_all, eB_eq, List.all_map]
    refine all_congr_mem fun Y hYm => ?_
    obtain ⟨B, hB⟩ := hX Y hYm
    rw [Function.comp_apply]
    exact commTT_eq hA hB

theorem norm_true : normCount = 192 := by
  obtain ⟨Ls, hL⟩ := eb_perms
  have hX := forall₂_mem_left hL
  unfold normCount
  rw [c_enum.2.1, countP_hRec (hi := 30) (q := fun i => normB 13 (mask 13) bsJ ebL (J3RC.T i))
    (by rw [c_hd.2.1]) (fun i hi => ?_)]
  · exact Nat.eq_of_beq_eq_true c_norm
  · obtain ⟨A, hA⟩ := hasP_of_mj (c_enum.2.2 i hi)
    unfold normB normPred spanTabs
    rw [listRec_all, eB_eq, List.all_map, len_ebL]
    refine all_congr_mem fun Y hYm => ?_
    obtain ⟨B, hB⟩ := hX Y hYm
    rw [Function.comp_apply, anyMaskB_eq, List.any_map, show (2 : Nat) ^ (ebL.length) = 16 from rfl]
    refine any_congr_mem fun c _ => ?_
    have hr : Rep 6156 (conjT 6156 (tab (J3RC.T i)) (invT 6156 (tab (J3RC.T i))) (tab Y))
        (A * B * A⁻¹) :=
      ((rep_tab hA).compT (rep_tab hB)).compT (CFSG.KS.Tbl.invT_rep (by norm_num) (rep_tab hA))
    rw [Function.comp_apply, tblEq_eq hr (rep_maskProd ebL Ls hL c), spanCompB_eq hL hA hB hA c]
    exact Bool.eq_iff_iff.2 (by simp [mul_inv_eq_iff_eq_mul])

theorem normOK_true : normOK 6156 3000 mGens [omT] = true := by
  unfold normOK
  rw [m_enum.2.1]
  have hT := m_enum.2.2
  refine conjAll_of (K := 1) (C := omC) (CI := omCI) (POS := J3RMNp)
    (fun i hi => (hT i hi).1) ⟨rfl, fun j hj => ?_⟩
    (fun j _ => ⟨cls_inv (by norm_num), (clsI_mj (by norm_num)).1⟩) (fun c hc => ?_)
  · have : j = 0 := by omega
    subst this
    refine ⟨?_, (cls_mj (by norm_num)).1⟩
    rw [show ([omT].toArray)[0]! = omT from rfl]
    unfold omT omC
    exact clsTbl_tab (by norm_num)
  · refine findPtK_conj_of_B mj_faith hT (fun _ _ => cls_mj (by norm_num))
      (fun _ _ => clsI_mj (by norm_num)) hc ?_
    exact bounded_spec (B := 320) (N := 3) (by simp [m_hd.2.1]) mNp_all c (by simpa using hc)

theorem le_true : eB.all (memT 6156 (mulClosureH 6156 mGens.toArray 3000).1) = true := by
  rw [m_enum.2.1, eB_eq, List.all_map]
  have hT := m_enum.2.2
  have key : ∀ j < 4, memT 6156 (hRec 6156 13 J3RM.cnt J3RM.T J3RM.PL).1 (tab (tbP j)) = true := by
    intro j hj
    have h := allN_spec m_le j hj
    simp only [CFSG.KS.Raw.Orb.strictB_eq, bAnd_iff, Nat.blt_eq] at h
    obtain ⟨hq, ha⟩ := h
    have e := mj_faith.eq_comp (hT _ hq) (mj_tbP (by omega)) mj_faith.id ha
    rw [CFSG.KC.J2Models.pcomp_idR (tb_facts (by omega)).1] at e
    refine memT_of hq ?_
    rw [e]
    exact tblEq_self (tb_facts (by omega)).1
  rw [ebL, List.all_cons, List.all_cons, List.all_cons, List.all_cons, List.all_nil,
    Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply]
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num)
  have k3 := key 3 (by norm_num)
  rw [tbP_zero] at k0
  rw [tbP_cls (k := 0) (by norm_num)] at k1
  rw [tbP_cls (k := 1) (by norm_num)] at k2
  rw [tbP_cls (k := 2) (by norm_num)] at k3
  rw [k0, k1, k2, k3]
  rfl

theorem clsB_all : ∀ i < J3RS.cnt, clsB i = true := by
  intro i hi
  rw [s_hd.2.1] at hi
  rcases Nat.lt_or_ge i 64 with h | h
  · simpa using allBlk_spec cls_ok0 i h
  · have := allBlk_spec cls_ok1 (i - 64) (by omega)
    rwa [show Nat.add 64 (i - 64) = i by simp only [Nat.add_eq]; omega] at this

theorem cls_true : clsOK = true := by
  obtain ⟨Ls, hL⟩ := eb_perms
  have hT := s_enum.2.2
  obtain ⟨Sp, hS⟩ := hasP_of_mj (cls_mj (k := 4) (by norm_num))
  unfold clsOK inConj spanTabs
  simp only []
  rw [s_enum.2.1, eB_eq, len_ebL, Array.all_eq_true]
  intro i hi
  have hi' : i < J3RS.cnt := by simpa [hRec] using hi
  have hx : (hRec 6156 13 J3RS.cnt J3RS.T J3RS.PL).1[i]'hi = tab (J3RS.T i) := by simp [hRec]
  rw [hx, ← clsB_all i hi']
  obtain ⟨A, hA⟩ := hasP_of_mj (hT i hi')
  unfold clsB
  rw [tblEq_sq hA, List.any_map, List.any_map, anyMaskB_eq, anyMaskB_eq,
    show (2 : Nat) ^ 4 = 16 by norm_num]
  have e1 : (List.range 16).any (tblEq 6156 (tab (J3RS.T i)) ∘ maskProd 6156 (List.map tab ebL)) =
      (List.range 16).any (spanEqB 13 (mask 13) bsJ ebL (J3RS.T i)) :=
    any_congr_mem fun c _ => by
      rw [Function.comp_apply, tblEq_eq (rep_tab hA) (rep_maskProd ebL Ls hL c), spanEqB_eq hL hA c]
  have e2 : (List.range 16).any ((fun u => tblEq 6156 (compT 6156 scT u)
      (compT 6156 (tab (J3RS.T i)) scT)) ∘ maskProd 6156 (List.map tab ebL)) =
      (List.range 16).any (conjSpanB 13 (mask 13) bsJ ebL (J3ClsP 4) (J3RS.T i)) :=
    any_congr_mem fun c _ => by
      rw [Function.comp_apply]
      unfold scT
      rw [clsTbl_tab (by norm_num), tblEq_eq ((rep_tab hS).compT (rep_maskProd ebL Ls hL c))
        ((rep_tab hA).compT (rep_tab hS)), conjSpanB_eq hL hS hA c]
  have e3 : (hRec 6156 13 J3RS.cnt J3RS.T J3RS.PL).1.toList.countP (invComm (tab (J3RS.T i))) =
      cntBelowK J3RS.cnt (fun j => sqB 13 (mask 13) bsJ (J3RS.T j) &&
        commB 13 (mask 13) bsJ (J3RS.T j) (J3RS.T i)) 2 := by
    refine countP_hRec (by rw [s_hd.2.1]) fun j hj => ?_
    obtain ⟨B, hB⟩ := hasP_of_mj (hT j hj)
    unfold invComm
    rw [tblEq_sq hB, commTT_eq hB hA]
  rw [e1, e2, e3]
  congr 1

open Certificates in
open CFSG.SectionRank.QTK.Insp443.J3Cls in
open CFSG.Sporadic.SmallOddCore (enumOK normOK centCount) in
open CFSG.Sporadic.SmallOddCore.Native (memT mulClosureH) in
open CFSG.Quasithin.KGC31.Native (ebasisOK masksOK) in
theorem facts589304 : tblsOK = true ∧ ebasisOK 6156 eB = true ∧
    masksOK 6156 eB omT [2, 3, 8, 12] = true ∧ masksOK 6156 eB (clsTbl 5) [3, 1, 10, 15] = true ∧
    masksOK 6156 eB (clsTbl 6) [10, 15, 3, 1] = true ∧
    enumOK 6156 3000 1920 cGens = true ∧ centCount 6156 3000 cGens eB = 16 ∧
    normCount = 192 ∧ enumOK 6156 3000 960 mGens = true ∧ enumOK 6156 3000 2880 nGens = true ∧
    normOK 6156 3000 mGens [omT] = true ∧
    eB.all (memT 6156 (mulClosureH 6156 mGens.toArray 3000).1) = true ∧
    enumOK 6156 3000 128 sGens = true ∧ clsOK = true :=
  ⟨tbls_true, eb_true, masks_true.1, masks_true.2.1, masks_true.2.2, c_enum.1, cent_true,
    norm_true, m_enum.1, n_enum.1, normOK_true, le_true, s_enum.1, cls_true⟩

end CertificateChecks.KernelJ3Ref

end
