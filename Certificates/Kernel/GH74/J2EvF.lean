module

public import Certificates.Kernel.GH74.J2Ev
public import Certificates.Kernel.GH74.Glue
public import Certificates.Kernel.Sporadic.OddCore.J2CnF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2Ev

open Subgroup
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn
open scoped commutatorElement

theorem base : (∀ j < 2, J2KB.GI j = J2XT j ∧ J2KB.G j = pidn 315 9) ∧
    (∀ j < 5, J2CB.GI j = F (Nat.add 18 j) ∧ J2CB.G j = pidn 315 9) ∧
    (∀ j < 4, J2E16.GI j = J2XT (Nat.add 4 j) ∧ J2E16.G j = pidn 315 9) ∧
    J2KB.cnt = 60 ∧ J2CB.cnt = 240 ∧ J2E16.cnt = 16 ∧
    penumHdK idK J2KB.cnt 3000 J2KB.T J2KB.PL = true ∧
    penumHdK idK J2CB.cnt 3000 J2CB.T J2CB.PL = true ∧
    penumHdK idK J2E16.cnt 3000 J2E16.T J2E16.PL = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, Nat.eq_of_beq_eq_true a4,
    Nat.eq_of_beq_eq_true a5, Nat.eq_of_beq_eq_true a6, a7, a8, a9⟩
  · have := allN_spec a1 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := allN_spec a2 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := allN_spec a3 j hj
    simp only [bAnd_iff] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem xp {j : Nat} (hj : j < 8) : canonK 315 9 (mask 9) (315 * 9) (J2XT j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2XI j) = true ∧
    invEqK 315 9 (mask 9) (315 * 9) (J2XT j) (J2XI j) = true := by
  have := allN_spec J2X.x_perm j hj
  simp only [bAnd_iff] at this
  exact this

theorem x_tabs : j2KbA = tabT (unpack 315 9 (J2XT 0)) ∧ j2KbB = tabT (unpack 315 9 (J2XT 1)) ∧
    j2VA = tabT (unpack 315 9 (J2XT 2)) ∧ j2VB = tabT (unpack 315 9 (J2XT 3)) ∧
    j2E0 = tabT (unpack 315 9 (J2XT 4)) ∧ j2E1 = tabT (unpack 315 9 (J2XT 5)) ∧
    j2E2 = tabT (unpack 315 9 (J2XT 6)) ∧ j2E3 = tabT (unpack 315 9 (J2XT 7)) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := J2X.x_eq
  exact ⟨tab_of_list a0, tab_of_list a1, tab_of_list a2, tab_of_list a3, tab_of_list a4,
    tab_of_list a5, tab_of_list a6, tab_of_list a7⟩

theorem kb_tabs : TabsOK 315 9 2 J2KB.GI j2KbGens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [(base.1 j hj).1]
  refine ⟨?_, (xp (by omega)).1⟩
  interval_cases j
  · exact x_tabs.1
  · exact x_tabs.2.1

theorem e_tabs : TabsOK 315 9 4 J2E16.GI j2E16Gens.toArray := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [(base.2.2.1 j hj).1]
  refine ⟨?_, (xp (by change 4 + j < 8; omega)).1⟩
  obtain ⟨-, -, -, -, e0, e1, e2, e3⟩ := x_tabs
  interval_cases j
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem cg2B : j2Row2B.centGens = J2Cn.cgL 18 5 := rfl

theorem cg2A : j2Row2A.centGens = j2C2Gens := rfl

theorem cb_tabs : TabsOK 315 9 5 J2CB.GI j2Row2B.centGens.toArray := by
  rw [cg2B]
  exact TabsOK_congr (fun j hj => (base.2.1 j hj).1) (cg_tabs 18 5 (by norm_num))

theorem kb_invs : ∀ j < 2, invEqK 315 9 (mask 9) (315 * 9) (J2KB.GI j) (J2XI j) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2XI j) = true := fun j hj => by
  rw [(base.1 j hj).1]
  exact ⟨(xp (by omega)).2.2, (xp (by omega)).2.1⟩

theorem e_invs : ∀ j < 4, invEqK 315 9 (mask 9) (315 * 9) (J2E16.GI j) (J2XI (Nat.add 4 j)) = true ∧
    canonK 315 9 (mask 9) (315 * 9) (J2XI (Nat.add 4 j)) = true := fun j hj => by
  rw [(base.2.2.1 j hj).1]
  exact ⟨(xp (by change 4 + j < 8; omega)).2.2, (xp (by change 4 + j < 8; omega)).2.1⟩

theorem cb_invs : ∀ j < 5, invEqK 315 9 (mask 9) (315 * 9) (J2CB.GI j) (J2CentI (Nat.add 18 j)) =
    true ∧ canonK 315 9 (mask 9) (315 * 9) (J2CentI (Nat.add 18 j)) = true := fun j hj => by
  rw [(base.2.1 j hj).1]
  exact invs_range 18 5 (by norm_num) j hj

theorem kb_pe : ∀ i < J2KB.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2KB.G J2KB.GI 2 J2KB.cnt
    J2KB.T J2KB.PL J2KB.POS J2KB.SRT J2KB.SRI i = true :=
  fun i hi => penumSl_spec kbE i (Nat.zero_le _) (by omega) hi
theorem kb_hs : ∀ i < J2KB.cnt, hsortPtK 315 9 (mask 9) J2KB.cnt J2KB.T J2KB.HS J2KB.HSI i = true :=
  fun i hi => slK_spec kbH i (Nat.zero_le _) (by omega) hi
theorem kb_cl : ∀ c < J2KB.cnt * (2 + 2), findPtK J2KB.cnt J2KB.T
    (prodQK 315 9 (mask 9) (2 + 2) J2KB.T (bothK 2 J2KB.GI J2XI)) J2KBCl c = true :=
  fun c hc => slK_spec kbCl c (Nat.zero_le _) (by change c < Nat.mul J2KB.cnt 4; omega)
    (by change c < Nat.mul J2KB.cnt 4; omega)

theorem cb_pe : ∀ i < J2CB.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2CB.G J2CB.GI 5 J2CB.cnt
    J2CB.T J2CB.PL J2CB.POS J2CB.SRT J2CB.SRI i = true :=
  fun i hi => penumSl_spec cbE i (Nat.zero_le _) (by omega) hi
theorem cb_hs : ∀ i < J2CB.cnt, hsortPtK 315 9 (mask 9) J2CB.cnt J2CB.T J2CB.HS J2CB.HSI i = true :=
  fun i hi => slK_spec cbH i (Nat.zero_le _) (by omega) hi
theorem cb_cl : ∀ c < J2CB.cnt * (5 + 5), findPtK J2CB.cnt J2CB.T
    (prodQK 315 9 (mask 9) (5 + 5) J2CB.T (bothK 5 J2CB.GI (fun j => J2CentI (Nat.add 18 j))))
      J2CBCl c = true :=
  fun c hc => slK_spec cbCl c (Nat.zero_le _) (by change c < Nat.mul J2CB.cnt 10; omega)
    (by change c < Nat.mul J2CB.cnt 10; omega)

theorem e_pe : ∀ i < J2E16.cnt, penumPtK 315 9 (mask 9) (315 * 9) true J2E16.G J2E16.GI 4
    J2E16.cnt J2E16.T J2E16.PL J2E16.POS J2E16.SRT J2E16.SRI i = true :=
  fun i hi => penumSl_spec eE i (Nat.zero_le _) (by omega) hi
theorem e_hs : ∀ i < J2E16.cnt, hsortPtK 315 9 (mask 9) J2E16.cnt J2E16.T J2E16.HS J2E16.HSI i =
    true :=
  fun i hi => slK_spec eH i (Nat.zero_le _) (by omega) hi
theorem e_cl : ∀ c < J2E16.cnt * (4 + 4), findPtK J2E16.cnt J2E16.T
    (prodQK 315 9 (mask 9) (4 + 4) J2E16.T (bothK 4 J2E16.GI (fun j => J2XI (Nat.add 4 j))))
      J2E16Cl c = true :=
  fun c hc => slK_spec eCl c (Nat.zero_le _) (by change c < Nat.mul J2E16.cnt 8; omega)
    (by change c < Nat.mul J2E16.cnt 8; omega)

theorem kb_enum : enumOK 315 cap j2KbGens 60 = true :=
  evEnum_of_rec hn (fun j hj => (base.1 j hj).2) kb_tabs kb_invs base.2.2.2.2.2.2.1 kb_pe kb_hs
    kb_cl base.2.2.2.1

theorem cb_enum : enumOK 315 cap j2Row2B.centGens 240 = true :=
  evEnum_of_rec hn (fun j hj => (base.2.1 j hj).2) cb_tabs cb_invs base.2.2.2.2.2.2.2.1 cb_pe cb_hs
    cb_cl base.2.2.2.2.1

theorem e_enum : enumOK 315 cap j2E16Gens 16 = true :=
  evEnum_of_rec hn (fun j hj => (base.2.2.1 j hj).2) e_tabs e_invs base.2.2.2.2.2.2.2.2 e_pe e_hs
    e_cl base.2.2.2.2.2.1

theorem c2_enum' : enumOK 315 cap j2Row2A.centGens 1920 = true := by
  rw [cg2A]
  refine KernelSpor.M12Syl.evEnum_of J2Loc.c2_enum ?_
  simp only [j2C2Gens, List.all_cons, List.all_nil, permF (by norm_num : 32 < 42),
    permF (by norm_num : 33 < 42), permF (by norm_num : 34 < 42), permF (by norm_num : 35 < 42)]
  rfl

theorem kb_arr : j2Kb = (hRec 315 9 J2KB.cnt J2KB.T J2KB.PL).1 :=
  closArr_eq (cap := cap) hn (fun j hj => (base.1 j hj).2) kb_tabs base.2.2.2.2.2.2.1 kb_pe kb_hs

theorem cb_arr : j2C2B = (hRec 315 9 J2CB.cnt J2CB.T J2CB.PL).1 :=
  closArr_eq (cap := cap) hn (fun j hj => (base.2.1 j hj).2) cb_tabs base.2.2.2.2.2.2.2.1 cb_pe cb_hs

theorem e_arr : j2E16 = (hRec 315 9 J2E16.cnt J2E16.T J2E16.PL).1 :=
  closArr_eq (cap := cap) hn (fun j hj => (base.2.2.1 j hj).2) e_tabs base.2.2.2.2.2.2.2.2 e_pe e_hs

theorem c2_arr : j2C2A = (hRec 315 9 J2C2.cnt J2C2.T J2C2.PL).1 := by
  unfold j2C2A
  rw [cg2A]
  exact closArr_eq (cap := cap) hn (J2Loc.ids_of J2Loc.idv.1.2.2.2) J2Loc.c2_tabs J2Loc.hd.1.2.2.2
    J2Loc.c2_pe J2Loc.c2_hs

theorem facts : sK (J2XT 0) = true ∧ sK (J2XT 1) = true ∧ (∀ j < 4, sK (J2XT (Nat.add 4 j)) = true) ∧
    involK (J2XT 2) = true ∧ bIf(sK (J2XT 2), false, true) = true ∧ sK (pc (J2XT 2) (F 0)) = true ∧
    J2Cn.commK (J2XT 2) (F 31) = true ∧
    involK (J2XT 3) = true ∧ bIf(sK (J2XT 3), false, true) = true ∧ sK (pc (J2XT 3) (F 0)) = true ∧
    J2Cn.commK (J2XT 3) (F 17) = true ∧ ∀ c < 43, atK J2KB.cnt J2KB.T J2KBP c (kbQ c) = true := by
  have h := facts_ok
  simp only [bAnd_iff] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨a1, a2, allN_spec a3, a4, a5, a6, a7, a8, a9, a10, a11, allN_spec a12⟩

theorem kbQ_mem {c : Nat} (hc : c < 43) : memT 315 j2Kb (tabT (unpack 315 9 (kbQ c))) = true := by
  have h := facts.2.2.2.2.2.2.2.2.2.2.2 c hc
  unfold atK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [kb_arr, ← Nat.eq_of_beq_eq_true h2]
  exact memT_of (Nat.le_of_ble_eq_true h1) (tblEq_self (penumPt_canon (kb_pe _ (Nat.le_of_ble_eq_true h1))))

theorem reps_ok : j2RepsOK = true := by
  unfold j2RepsOK
  rw [show j2Row2A.rep = j2CentTbl 31 from rfl, show j2Row2B.rep = j2CentTbl 17 from rfl,
    j2OuterTbl, permF (by norm_num : 0 < 42), permF (by norm_num : 31 < 42),
    permF (by norm_num : 17 < 42)]
  rfl

theorem c2A_ok : j2C2AEnumOK = true := by
  have hinv : invsOK 315 j2C2A = true := invsOK_of_enumOK (by norm_num) c2_enum'
  unfold j2C2AEnumOK
  rw [c2_enum', hinv]
  rfl

theorem c2B_ok : j2C2BEnumOK = true := by
  have hinv : invsOK 315 j2C2B = true := invsOK_of_enumOK (by norm_num) cb_enum
  unfold j2C2BEnumOK
  rw [cb_enum, hinv]
  rfl

theorem xs {j : Nat} (hj : j < 8) : j2Sift (tabT (unpack 315 9 (J2XT j))) = sK (J2XT j) :=
  sift_eq (xp hj).1

theorem kb_ok : j2KbEnumOK = true := by
  unfold j2KbEnumOK
  rw [kb_enum]
  simp only [j2KbGens, List.all_cons, List.all_nil]
  rw [x_tabs.1, x_tabs.2.1, xs (by norm_num), xs (by norm_num)]
  simp only [facts.1, facts.2.1]
  rfl

theorem bIf_not (b : Bool) : bIf(b, false, true) = !b := by cases b <;> rfl

theorem outer_ok : j2OuterOK = true := by
  obtain ⟨-, -, va, vb, -⟩ := x_tabs
  obtain ⟨-, -, -, f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := facts
  have c2 := (xp (j := 2) (by norm_num)).1
  have c3 := (xp (j := 3) (by norm_num)).1
  unfold j2OuterOK outerCommOK
  rw [show j2Row2A.rep = j2CentTbl 31 from rfl, show j2Row2B.rep = j2CentTbl 17 from rfl,
    j2OuterTbl, tabF (by norm_num : 0 < 42), tabF (by norm_num : 31 < 42),
    tabF (by norm_num : 17 < 42), va, vb, permOK_unpack c2 (xp (j := 2) (by norm_num)).2.2,
    permOK_unpack c3 (xp (j := 3) (by norm_num)).2.2, involF c2, involF c3, sift_eq c2,
    sift_eq c3, compT_unpack c2 (Fc (by norm_num)), compT_unpack c3 (Fc (by norm_num)),
    sift_eq (CFSG.KC.BfsPin.canonK_pcomp c2 (Fc (by norm_num))),
    sift_eq (CFSG.KC.BfsPin.canonK_pcomp c3 (Fc (by norm_num))),
    commF c2 (Fc (by norm_num)), commF c3 (Fc (by norm_num))]
  rw [bIf_not] at f2 f6
  change (true && involK (J2XT 2) && !sK (J2XT 2) && sK (pc (J2XT 2) (F 0)) &&
    J2Cn.commK (J2XT 2) (F 31) && (true && involK (J2XT 3) && !sK (J2XT 3) &&
    sK (pc (J2XT 3) (F 0)) && J2Cn.commK (J2XT 3) (F 17))) = true
  rw [f1, f2, f3, f4, f5, f6, f7, f8]
  rfl

theorem e_conj {j l : Nat} (hj : j < 4) (hl : l < 2) :
    conjT 315 (tabT (unpack 315 9 (J2XT (Nat.add 4 j))))
        (invT 315 (tabT (unpack 315 9 (J2XT (Nat.add 4 j))))) (tabT (unpack 315 9 (J2XT l))) =
      tabT (unpack 315 9 (kbQ (35 + 2 * j + l))) := by
  have hE := xp (j := Nat.add 4 j) (by change 4 + j < 8; omega)
  have hX := xp (j := l) (by omega)
  have e : kbQ (35 + 2 * j + l) = pc (pc (J2XT (Nat.add 4 j)) (J2XT l)) (J2XI (Nat.add 4 j)) := by
    interval_cases j <;> interval_cases l <;> rfl
  rw [e, invT_unpack (by norm_num) hE.2.2]
  exact conjT_unpack hE.1 hE.2.1 hX.1

theorem e16_ok : j2E16OK = true := by
  obtain ⟨xa, xb, -, -, e0, e1, e2, e3⟩ := x_tabs
  have hab := e16_ab
  unfold j2E16OK
  rw [e_enum]
  simp only [j2E16Gens, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and]
  rw [e0, e1, e2, e3, xa, xb]
  have hs : ∀ j < 4, j2Sift (tabT (unpack 315 9 (J2XT (Nat.add 4 j)))) = true := fun j hj => by
    rw [xs (by change 4 + j < 8; omega)]
    exact facts.2.2.1 j hj
  have hc : ∀ j < 4, conjInOK 315 j2Kb (tabT (unpack 315 9 (J2XT 0)))
      (tabT (unpack 315 9 (J2XT 1))) (tabT (unpack 315 9 (J2XT (Nat.add 4 j)))) = true := by
    intro j hj
    unfold conjInOK
    rw [e_conj hj (by norm_num : 0 < 2), e_conj hj (by norm_num : 1 < 2), kbQ_mem (by omega),
      kbQ_mem (by omega)]
    rfl
  have hel : elemAbOK 315 j2E16 = true := by
    unfold elemAbOK
    rw [e_arr, all_hRec_iff]
    intro i hi
    have hT := penumPt_canon (e_pe i hi)
    have h := allN_spec hab i hi
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [compT_unpack hT hT, hid, tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp hT hT) hidc,
      Bool.and_eq_true, all_hRec_iff]
    refine ⟨h1, fun j hj => ?_⟩
    rw [commF hT (penumPt_canon (e_pe j hj))]
    exact allN_spec h2 j hj
  rw [hs 0 (by norm_num), hs 1 (by norm_num), hs 2 (by norm_num), hs 3 (by norm_num), hel,
    hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), hc 3 (by norm_num)]
  rfl

end CertificateChecks.KernelGH74.J2Ev

end
