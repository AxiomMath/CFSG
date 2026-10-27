module

public import Certificates.Kernel.Sporadic.HS.L2273S
public import Certificates.Kernel.Sporadic.HS.L2273C
public import Certificates.Kernel.LocalQT.HSAut.F4146
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3
public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.HSCosetInputs
public meta import CFSG.Sporadic.SmallOddCore.HSData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HSL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KS.HSL
open CFSG.KD.LQT.C4126 CFSG.KS.Mathieu CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.PSL3Four

abbrev Cn (p : Nat) : Prop := canonK 3850 12 (mask 12) (3850 * 12) p = true

theorem cPc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KD.LQT.HN.cPc hp hq

theorem comp_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    comp 3850 (unpack 3850 12 p) (unpack 3850 12 q) = unpack 3850 12 (pc p q) :=
  CFSG.KD.LQT.HN.comp_pc hp hq

theorem beq_pc {p q : Nat} (hp : Cn p) (hq : Cn q) :
    (unpack 3850 12 p == unpack 3850 12 q) = Nat.beq p q :=
  CFSG.KD.LQT.HN.beq_pc hp hq

theorem nget_getD' (L : List Nat) (i : Nat) : nget L i = L.getD i 0 := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem bIf_eq_of {q f r : Bool} (hfq : f = true → q = true) (hr : r = f) :
    r = Bool.rec (motive := fun _ => Bool) false f q := by
  cases q <;> cases f <;> simp_all

theorem base : (∀ k < 4, Cn (c2L k)) ∧ (∀ k < 2, Cn (HCI (Nat.add k 6))) ∧
    (∀ k < 4, Cn (HCI (Nat.add k 13))) ∧ Cn idn ∧
    ∀ i < 8, Cn (CS i) ∧ Cn (CSI i) ∧
      invEqK 3850 12 (mask 12) (3850 * 12) (CS i) (CSI i) = true := by
  have h := base_ok
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨allN_spec h1, allN_spec h2, allN_spec h3, h4, fun i hi => ?_⟩
  have h6 := allN_spec h5 i hi
  simp only [bAnd_iff] at h6
  exact h6

theorem inv_facts {p r : Nat} (h : invEqK 3850 12 (mask 12) (3850 * 12) p r = true) :
    invTab 3850 (unpack 3850 12 p) = unpack 3850 12 r ∧
      comp 3850 (unpack 3850 12 r) (unpack 3850 12 p) = idTab 3850 :=
  ⟨(invEqK_sound h).1, CFSG.KD.LQT.HN.comp_inv_id (invEqK_sound h).2⟩

theorem invsOK_of {gens ginv : Array Tab} (hsz : ginv.size = gens.size)
    (h : ∀ k < gens.size, ginv[k]!.size = 3850 ∧ comp 3850 ginv[k]! gens[k]! = idTab 3850) :
    invsOK 3850 gens ginv = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true]
  exact ⟨hsz, fun k hk => h k hk⟩

theorem getElem!_map_inv {A : Array Tab} {k : Nat} (hk : k < A.size) :
    (A.map (invTab 3850))[k]! = invTab 3850 A[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, ← getElem!_pos A k hk]

theorem c1_get {j : Nat} (hj : j < 2) : hsC1Tabs[j]! = unpack 3850 12 (c1L j) ∧ Cn (c1L j) := by
  obtain ⟨-, c6, c7, -⟩ := CFSG.KD.LQT.HN.canons
  rw [hsC1Tabs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  interval_cases j
  · exact ⟨hsCentTbl_eq (by norm_num), c6⟩
  · exact ⟨hsCentTbl_eq (by norm_num), c7⟩

theorem c2_get {j : Nat} (hj : j < 4) : hsC2Tabs[j]! = unpack 3850 12 (c2L j) ∧ Cn (c2L j) := by
  rw [hsC2Tabs, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact ⟨hsCentTbl_eq (by omega), base.1 j hj⟩

theorem c1I_get {j : Nat} (hj : j < 2) : hsC1Invs[j]! = unpack 3850 12 (HCI (Nat.add j 6)) ∧
    Cn (HCI (Nat.add j 6)) ∧ comp 3850 hsC1Invs[j]! hsC1Tabs[j]! = idTab 3850 := by
  have hi := inv_facts (p := c1L j) (r := HCI (Nat.add j 6)) (allN_spec hc_perms (j + 6) (by omega))
  rw [hsC1Invs, getElem!_map_inv (by simpa [hsC1Tabs] using hj), (c1_get hj).1, hi.1]
  exact ⟨rfl, base.2.1 j hj, hi.2⟩

theorem c2I_get {j : Nat} (hj : j < 4) : hsC2Invs[j]! = unpack 3850 12 (HCI (Nat.add j 13)) ∧
    Cn (HCI (Nat.add j 13)) ∧ comp 3850 hsC2Invs[j]! hsC2Tabs[j]! = idTab 3850 := by
  have hi := inv_facts (p := c2L j) (r := HCI (Nat.add j 13))
    (allN_spec hc_perms (j + 13) (by omega))
  rw [hsC2Invs, getElem!_map_inv (by simpa [hsC2Tabs] using hj), (c2_get hj).1, hi.1]
  exact ⟨rfl, base.2.2.1 j hj, hi.2⟩

theorem word_c1 (wd : List Nat) (hw : ∀ i ∈ wd, i < 2) :
    wordTabS 3850 hsC1Tabs wd = unpack 3850 12 (wk c1L wd) ∧ Cn (wk c1L wd) :=
  wordTabK_eq CFSG.KD.LQT.HN.idTab_eq base.2.2.2.1 wd fun i hi => c1_get (hw i hi)

theorem word_c2 (wd : List Nat) (hw : ∀ i ∈ wd, i < 4) :
    wordTabS 3850 hsC2Tabs wd = unpack 3850 12 (wk c2L wd) ∧ Cn (wk c2L wd) :=
  wordTabK_eq CFSG.KD.LQT.HN.idTab_eq base.2.2.2.1 wd fun i hi => c2_get (hw i hi)

theorem normal_of {gens ginv gs : Array Tab} {kG kS cnt k : Nat}
    {L LI S T PL POS SRT SRI G GI N1 N2 : Nat → Nat}
    (hg : gens.size = kG) (hgi : ginv.size = kG) (hs : gs.size = kS)
    (hgl : ∀ j < kG, gens[j]! = unpack 3850 12 (L j) ∧ Cn (L j))
    (hgil : ∀ j < kG, ginv[j]! = unpack 3850 12 (LI j) ∧ Cn (LI j) ∧
      comp 3850 ginv[j]! gens[j]! = idTab 3850)
    (hsl : ∀ i < kS, gs[i]! = unpack 3850 12 (S i) ∧ Cn (S i))
    (hpt : ∀ i < cnt, penumPtK 3850 12 (mask 12) (3850 * 12) false G GI k cnt T PL POS SRT SRI i =
      true)
    (hn : ∀ j < kG, ∀ i < kS,
      strictB (N1 (Nat.add (Nat.mul j kS) i)) (fun q => bAnd(Nat.blt q cnt,
        Nat.beq (T q) (pc (pc (L j) (S i)) (LI j)))) = true ∧
      strictB (N2 (Nat.add (Nat.mul j kS) i)) (fun q => bAnd(Nat.blt q cnt,
        Nat.beq (T q) (pc (pc (LI j) (S i)) (L j)))) = true) :
    normalOK 3850 (penumRec 3850 12 cnt T PL).tabs gens ginv gs = true := by
  unfold normalOK
  simp only [Bool.and_eq_true]
  refine ⟨invsOK_of (by rw [hg, hgi]) fun j hj => ?_, ?_⟩
  · rw [hg] at hj
    obtain ⟨e, -, hc⟩ := hgil j hj
    refine ⟨?_, hc⟩
    rw [e]
    exact unpack_size _ _ _
  · rw [allBelow_eq_true]
    intro j hj
    rw [hg] at hj
    rw [allBelow_eq_true]
    intro i hi
    rw [hs] at hi
    obtain ⟨n1, n2⟩ := hn j hj i hi
    rw [strictB_app'] at n1 n2
    obtain ⟨q1, e1⟩ := (bAnd_iff _ _).1 n1
    obtain ⟨q2, e2⟩ := (bAnd_iff _ _).1 n2
    obtain ⟨hgj, cg⟩ := hgl j hj
    obtain ⟨hgij, cgi, -⟩ := hgil j hj
    obtain ⟨hsi, cs⟩ := hsl i hi
    rw [Bool.and_eq_true, hgj, hgij, hsi]
    unfold conjTab
    rw [comp_pc cg cs, comp_pc (cPc cg cs) cgi, comp_pc cgi cs, comp_pc (cPc cgi cs) cg]
    exact ⟨penum_found_sound hpt (Eq.mp Nat.blt_eq q1) (Nat.eq_of_beq_eq_true e1),
      penum_found_sound hpt (Eq.mp Nat.blt_eq q2) (Nat.eq_of_beq_eq_true e2)⟩

theorem notIn_of {cnt x : Nat} {T PL : Nat → Nat} (hT : ∀ q < cnt, Cn (T q)) (hx : Cn x)
    (h : notinK T cnt x = true) : notInOK (penumRec 3850 12 cnt T PL).tabs (unpack 3850 12 x) =
      true := by
  unfold notInOK
  rw [allBelow_eq_true]
  intro q hq
  have hq' : q < cnt := by simpa [penumRec] using hq
  rw [getElem!_pos _ q hq]
  simp only [penumRec, Array.getElem_ofFn]
  rw [beq_pc (hT q hq') hx]
  have hz := allN_spec h q hq'
  cases e : Nat.beq (T q) x
  · rfl
  · rw [e] at hz
    exact absurd hz (by decide)

theorem qwords_lt : ∀ j < 6, ∀ i ∈ hsQWords.getD j [], i < 2 := by decide

theorem qgens_get {j : Nat} (hj : j < 6) : hsQGens[j]! = unpack 3850 12 (Q.G j) ∧ Cn (Q.G j) := by
  have hq := allN_spec q_gens j hj
  simp only [bAnd_iff] at hq
  refine ⟨?_, hq.2⟩
  rw [hsQGens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true hq.1, lget2_eq]
  exact (word_c1 _ (qwords_lt j hj)).1

theorem q_ok : GensOK 3850 12 6 Q.G hsQGens := ⟨by simp [hsQGens], fun _ hj => qgens_get hj⟩

theorem q_hd' : penumHdK idn Q.cnt 64 Q.T Q.PL = true ∧ Q.cnt = 64 := by
  have h := q_hd
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem q_cnt : Q.cnt = 64 := q_hd'.2

theorem q_pt {i : Nat} (hi : i < Q.cnt) : penumPtK 3850 12 (mask 12) (3850 * 12) false Q.G Q.GI 6
    Q.cnt Q.T Q.PL Q.POS Q.SRT Q.SRI i = true := by
  have hc := q_cnt
  have hs : i / 8 < 8 := by omega
  have h : qSl (i / 8) = true := QS.all (i / 8) hs
  exact penumSl_spec h i (by change i / 8 * 8 ≤ i; omega) (by change i < i / 8 * 8 + 8; omega) hi

theorem q_enum : hsQEnum = penumRec 3850 12 Q.cnt Q.T Q.PL ∧
    enumOK 3850 hsQGens (penumRec 3850 12 Q.cnt Q.T Q.PL) = true :=
  penumK_left_sound (cap := 64) CFSG.KD.LQT.HN.hn q_ok q_hd'.1 (fun _ hi => q_pt hi)

theorem q_normal : normalOK 3850 (penumRec 3850 12 Q.cnt Q.T Q.PL).tabs hsC1Tabs hsC1Invs hsQGens =
    true :=
  normal_of (kG := 2) (kS := 6) (L := c1L) (LI := fun j => HCI (Nat.add j 6)) (S := Q.G)
    (N1 := NQ1) (N2 := NQ2) (by simp [hsC1Tabs]) (by simp [hsC1Invs, hsC1Tabs])
    (by simp [hsQGens]) (fun _ hj => c1_get hj) (fun _ hj => c1I_get hj)
    (fun _ hi => qgens_get hi) (fun _ hi => q_pt hi) fun j hj i hi => by
      have h := allN_spec (allN_spec q_norm j hj) i hi
      simp only [bAnd_iff] at h
      exact h

theorem c1tabs_eq : hsC1Tabs = CFSG.QuasithinUnique.Id2519.HSAut.gensA0 := by
  apply Array.ext (by simp [hsC1Tabs, CFSG.QuasithinUnique.Id2519.HSAut.gensA0])
  intro i h1 _
  have hi : i < 2 := by simpa [hsC1Tabs] using h1
  interval_cases i <;> simp [hsC1Tabs, CFSG.QuasithinUnique.Id2519.HSAut.gensA0]

theorem c1_enum : hsC1Enum = penumRec 3850 12 CFSG.KD.LQT.HN.A.cnt CFSG.KD.LQT.HN.A.T
    CFSG.KD.LQT.HN.A.PL := by
  rw [hsC1Enum, c1tabs_eq]
  exact CFSG.KD.LQT.HN.enum_eq.1

theorem quick_of_full {t : Nat}
    (h : allN 6 (fun j => Nat.beq (pc t (Q.G j)) (pc (Q.G j) t)) = true) :
    allN 6 (fun j => allN 2 (fun p => Nat.beq (img t (img (Q.G j) p)) (img (Q.G j) (img t p)))) =
      true := by
  refine allN_of fun j hj => allN_of fun p hp => ?_
  have e := congrArg (fun x => img x p) (Nat.eq_of_beq_eq_true (allN_spec h j hj))
  rw [CFSG.KD.LQT.HN.img_pc (by omega), CFSG.KD.LQT.HN.img_pc (by omega)] at e
  rw [e]
  exact Nat.beq_refl _

theorem comm_eq {t : Nat} (ht : Cn t) :
    commAll 3850 hsQGens (unpack 3850 12 t) = CFSG.KS.HSL.commK Q.G t := by
  have hfull : commAll 3850 hsQGens (unpack 3850 12 t) =
      allN 6 (fun j => Nat.beq (pc t (Q.G j)) (pc (Q.G j) t)) := by
    apply Bool.eq_iff_iff.2
    rw [allN_iff]
    unfold commAll
    rw [allBelow_eq_true]
    have hs : hsQGens.size = 6 := by simp [hsQGens]
    rw [hs]
    refine forall_congr' fun j => imp_congr_right fun hj => ?_
    obtain ⟨e, c⟩ := qgens_get hj
    rw [e, comp_pc ht c, comp_pc c ht, beq_pc (cPc ht c) (cPc c ht)]
  unfold CFSG.KS.HSL.commK
  exact bIf_eq_of quick_of_full hfull

theorem c1_filter : (hsC1Enum.tabs.toList.filter (commAll 3850 hsQGens)).length = 4 := by
  rw [c1_enum]
  have hc : CFSG.KD.LQT.HN.A.cnt = 7680 := CFSG.KD.LQT.HN.a_parts.2.2.2
  simp only [penumRec, Array.toList_ofFn]
  rw [ofFn_range CFSG.KD.LQT.HN.A.cnt (fun i => unpack 3850 12 (CFSG.KD.LQT.HN.A.T i)),
    List.filter_map, List.length_map, ← List.countP_eq_length_filter]
  have key : (List.range CFSG.KD.LQT.HN.A.cnt).countP
      ((commAll 3850 hsQGens) ∘ fun i => unpack 3850 12 (CFSG.KD.LQT.HN.A.T i)) =
      (List.range (64 * 120)).countP
        (fun i => CFSG.KS.HSL.commK Q.G (CFSG.KD.LQT.HN.A.T i)) := by
    rw [hc]
    apply List.countP_congr
    intro i hi
    have hi' : i < CFSG.KD.LQT.HN.A.cnt := by rw [hc]; simpa using hi
    rw [Function.comp_apply, comm_eq (penumPt_canon (CFSG.KD.LQT.HN.pt i hi').1)]
  rw [key, ← cntK_eq]
  exact Nat.eq_of_beq_eq_true c1_comm

theorem dwords_lt : ∀ j < 2, ∀ i ∈ hsDWords.getD j [], i < 4 := by decide

theorem dgens_get {j : Nat} (hj : j < 2) : hsDGens[j]! = unpack 3850 12 (D.G j) ∧ Cn (D.G j) := by
  have hq := allN_spec d_gens j hj
  simp only [bAnd_iff] at hq
  refine ⟨?_, hq.2.1⟩
  rw [hsDGens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true hq.1, lget2_eq]
  exact (word_c2 _ (dwords_lt j hj)).1

theorem dinvs_get {j : Nat} (hj : j < 2) : hsDInvs[j]! = unpack 3850 12 (O0.GI j) ∧
    Cn (O0.GI j) ∧ comp 3850 hsDInvs[j]! hsDGens[j]! = idTab 3850 := by
  have hq := allN_spec d_gens j hj
  simp only [bAnd_iff] at hq
  have hi := inv_facts hq.2.2.2
  rw [hsDInvs, getElem!_map_inv (by simpa [hsDGens] using hj), (dgens_get hj).1, hi.1]
  exact ⟨rfl, hq.2.2.1, hi.2⟩

theorem d_ok : GensOK 3850 12 2 D.G hsDGens := ⟨by simp [hsDGens], fun _ hj => dgens_get hj⟩

theorem d_hd' : penumHdK idn D.cnt 360 D.T D.PL = true ∧ D.cnt = 360 := by
  have h := d_hd
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem d_cnt : D.cnt = 360 := d_hd'.2

theorem d_pt {i : Nat} (hi : i < D.cnt) : penumPtK 3850 12 (mask 12) (3850 * 12) false D.G D.GI 2
    D.cnt D.T D.PL D.POS D.SRT D.SRI i = true := by
  have hc := d_cnt
  have hs : i / 16 < 23 := by omega
  have h : dSl (i / 16) = true := DS.all (i / 16) hs
  exact penumSl_spec h i (by change i / 16 * 16 ≤ i; omega)
    (by change i < i / 16 * 16 + 16; omega) hi

theorem d_enum : hsDEnum = penumRec 3850 12 D.cnt D.T D.PL ∧
    enumOK 3850 hsDGens (penumRec 3850 12 D.cnt D.T D.PL) = true :=
  penumK_left_sound (cap := 360) CFSG.KD.LQT.HN.hn d_ok d_hd'.1 (fun _ hi => d_pt hi)

theorem d_normal : normalOK 3850 (penumRec 3850 12 D.cnt D.T D.PL).tabs hsC2Tabs hsC2Invs hsDGens =
    true :=
  normal_of (kG := 4) (kS := 2) (L := c2L) (LI := fun j => HCI (Nat.add j 13)) (S := D.G)
    (N1 := ND1) (N2 := ND2) (by simp [hsC2Tabs]) (by simp [hsC2Invs, hsC2Tabs])
    (by simp [hsDGens]) (fun _ hj => c2_get hj) (fun _ hj => c2I_get hj)
    (fun _ hi => dgens_get hi) (fun _ hi => d_pt hi) fun j hj i hi => by
      have h := allN_spec (allN_spec d_norm j hj) i hi
      simp only [bAnd_iff] at h
      exact h

theorem d_canon {q : Nat} (hq : q < D.cnt) : Cn (D.T q) := penumPt_canon (d_pt hq)

@[expose] noncomputable def orbRec (l : Nat) : Enum := penumRec 3850 12 (oC l) (oT l) (oPL l)

theorem cwords_lt : ∀ l < 7, ∀ j ∈ hsDClassWords.getD l [], j < hsDGens.size := by decide

theorem o_facts {l : Nat} (hl : l < 7) : penumHdK (oR l) (oC l) 1000 (oT l) (oPL l) = true ∧
    oR l = wk D.G (lget2 hsDClassWords l) ∧ oC l = nget hsDClassSizes l := by
  have h := allN_spec o_hd l hl
  simp only [bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem rep_eq {l : Nat} (hl : l < 7) :
    wordTabS 3850 hsDGens (hsDClassWords.getD l []) = unpack 3850 12 (oR l) ∧ Cn (oR l) := by
  rw [(o_facts hl).2.1, lget2_eq]
  exact wordTabK_eq CFSG.KD.LQT.HN.idTab_eq base.2.2.2.1 _ fun j hj => by
    have hj2 : j < 2 := by simpa [hsDGens] using cwords_lt l hl j hj
    exact dgens_get hj2

theorem o_pt {l i : Nat} (hl : l < 7) (hi : i < oC l) : penumPtK 3850 12 (mask 12) (3850 * 12) true
    (oG l) (oGI l) 2 (oC l) (oT l) (oPL l) (oPOS l) (oSRT l) (oSRI l) i = true := by
  have hc : oC l ≤ 90 := by
    rw [(o_facts hl).2.2, nget_getD']
    interval_cases l <;> decide
  have hs : i / 2 < 45 := by omega
  have h : oSl (i / 2) = true := OS.all (i / 2) hs
  exact penumSl_spec (allN_spec h l hl) i (by change i / 2 * 2 ≤ i; omega)
    (by change i < i / 2 * 2 + 2; omega) hi

theorem o_canon {l q : Nat} (hl : l < 7) (hq : q < oC l) : Cn (oT l q) := penumPt_canon (o_pt hl hq)

theorem fg_ok {l : Nat} (hl : l < 7) : GensOK 3850 12 2 (oG l) hsDGens :=
  ⟨by simp [hsDGens], fun j hj => by
    have h := allN_spec (allN_spec o_gens l hl) j hj
    simp only [bAnd_iff] at h
    rw [Nat.eq_of_beq_eq_true h.1]
    exact dgens_get hj⟩

theorem fgi_ok {l : Nat} (hl : l < 7) : GensOK 3850 12 2 (oGI l) hsDInvs :=
  ⟨by simp [hsDInvs, hsDGens], fun j hj => by
    have h := allN_spec (allN_spec o_gens l hl) j hj
    simp only [bAnd_iff] at h
    rw [Nat.eq_of_beq_eq_true h.2]
    exact ⟨(dinvs_get hj).1, (dinvs_get hj).2.1⟩⟩

theorem orbits_get {l : Nat} (hl : l < 7) : hsDOrbits[l]! = orbitBFS 3850 hsDGens hsDInvs
    (wordTabS 3850 hsDGens (hsDClassWords.getD l [])) 1000 := by
  rw [getElem!_pos hsDOrbits l (by simp [hsDOrbits]; omega)]
  simp [hsDOrbits]

theorem orb_enum {l : Nat} (hl : l < 7) : hsDOrbits[l]! = orbRec l ∧
    treeOK (conjStep 3850 hsDGens hsDInvs) hsDGens.size
      (wordTabS 3850 hsDGens (hsDClassWords.getD l [])) (orbRec l) = true := by
  rw [orbits_get hl]
  have h := penumK_conj_sound (cap := 1000) CFSG.KD.LQT.HN.hn (fg_ok hl) (fgi_ok hl) (rep_eq hl).1
    (o_facts hl).1 (fun _ hi => o_pt hl hi)
  have hs : hsDGens.size = 2 := by simp [hsDGens]
  rw [hs]
  exact h

theorem orb_size {l : Nat} (hl : l < 7) : (orbRec l).tabs.size = hsDClassSizes.getD l 0 := by
  simp only [orbRec, penumRec, Array.size_ofFn]
  rw [(o_facts hl).2.2, nget_getD']

theorem invsD : invsOK 3850 hsDGens hsDInvs = true :=
  invsOK_of (by simp [hsDInvs]) fun k hk => by
    have hk2 : k < 2 := by simpa [hsDGens] using hk
    obtain ⟨e, -, hc⟩ := dinvs_get hk2
    refine ⟨?_, hc⟩
    rw [e]
    exact unpack_size _ _ _

theorem cover_at {k : Nat} (hk : k < D.cnt) :
    anyBelow hsDOrbits.size (fun l => found ((hsDOrbits.map fun e => indexOf e.tabs)[l]!)
      hsDOrbits[l]!.tabs (penumRec 3850 12 D.cnt D.T D.PL).tabs[k]!) = true := by
  have hc := allN_spec cover k (by rw [d_cnt] at hk; exact hk)
  unfold coverK at hc
  simp only [strictB_app'] at hc
  obtain ⟨hl, hq, he⟩ := (by simpa only [bAnd_iff] using hc :
    Nat.blt (Nat.shiftRight (COV k) 16) 7 = true ∧
    Nat.blt (Nat.land (COV k) 65535) (oC (Nat.shiftRight (COV k) 16)) = true ∧
    Nat.beq (oT (Nat.shiftRight (COV k) 16) (Nat.land (COV k) 65535)) (D.T k) = true)
  have hl' := Eq.mp Nat.blt_eq hl
  rw [anyBelow_eq_true]
  have hsz : Nat.shiftRight (COV k) 16 < hsDOrbits.size := by simpa [hsDOrbits] using hl'
  refine ⟨Nat.shiftRight (COV k) 16, hsz, ?_⟩
  rw [CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ hsz, (orb_enum hl').1,
    getElem!_pos _ k (by simpa [penumRec] using hk)]
  simp only [penumRec, Array.getElem_ofFn]
  exact penum_found_sound (fun _ hx => o_pt hl' hx) (Eq.mp Nat.blt_eq hq)
    (Nat.eq_of_beq_eq_true he)

theorem cs_get {i : Nat} (hi : i < 8) : hsCosTabs[i]! = unpack 3850 12 (CS i) ∧ Cn (CS i) := by
  refine ⟨?_, (base.2.2.2.2 i hi).1⟩
  have hw : ∀ i < 8, ∀ j ∈ hsCosWords.getD i [], j < 4 := by decide
  rw [hsCosTabs, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true (allN_spec cs_words i hi), lget2_eq]
  exact (word_c2 _ (hw i hi)).1

theorem csI_get {i : Nat} (hi : i < 8) : hsCosInvs[i]! = unpack 3850 12 (CSI i) ∧ Cn (CSI i) ∧
    comp 3850 hsCosInvs[i]! hsCosTabs[i]! = idTab 3850 := by
  obtain ⟨-, c2, h⟩ := base.2.2.2.2 i hi
  have hi' := inv_facts h
  rw [hsCosInvs, getElem!_map_inv (by simpa [hsCosTabs] using hi), (cs_get hi).1, hi'.1]
  exact ⟨rfl, c2, hi'.2⟩

theorem cosets : (∀ i < 8, ∀ j ∈ hsCosWords.getD i [], j < 4) ∧
    invsOK 3850 hsCosTabs hsCosInvs = true ∧
    (∀ i < 8, ∀ j < 8, i ≠ j →
      notInOK hsDEnum.tabs (comp 3850 hsCosInvs[i]! hsCosTabs[j]!) = true) ∧
    commAll 3850 hsDGens hsCosTabs[1]! = true ∧
    (∀ i < 6, notInOK hsDOrbits[hsCosCls.getD i 0]!.tabs
      (conjTab 3850 hsCosInvs[i + 2]! hsCosTabs[i + 2]!
        (wordTabS 3850 hsDGens (hsDClassWords.getD (hsCosCls.getD i 0) []))) = true) := by
  refine ⟨by decide, ?_, fun i hi j hj hij => ?_, ?_, fun i hi => ?_⟩
  · refine invsOK_of (by simp [hsCosInvs]) fun k hk => ?_
    have hk8 : k < 8 := by simpa [hsCosTabs] using hk
    obtain ⟨e, -, hc⟩ := csI_get hk8
    refine ⟨?_, hc⟩
    rw [e]
    exact unpack_size _ _ _
  · obtain ⟨ei, ci, -⟩ := csI_get hi
    obtain ⟨ej, cj⟩ := cs_get hj
    rw [d_enum.1, ei, ej, comp_pc ci cj]
    refine notIn_of (fun _ hq => d_canon hq) (cPc ci cj) ?_
    have h := allN_spec (allN_spec cs_dist i hi) j hj
    have hb : Nat.beq i j = false := by
      cases e : Nat.beq i j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hij
    rw [hb] at h
    exact h
  · unfold commAll
    rw [allBelow_eq_true]
    intro j hj
    have hj2 : j < 2 := by simpa [hsDGens] using hj
    obtain ⟨e1, c1⟩ := cs_get (i := 1) (by norm_num)
    obtain ⟨ed, cd⟩ := dgens_get hj2
    rw [e1, ed, comp_pc c1 cd, comp_pc cd c1, beq_pc (cPc c1 cd) (cPc cd c1)]
    exact allN_spec cs_comm j hj2
  · have h := allN_spec cs_bad i hi
    rw [strictB_app', nget_getD'] at h
    simp only [bAnd_iff] at h
    obtain ⟨hl, hn⟩ := h
    have hl' : hsCosCls.getD i 0 < 7 := Eq.mp Nat.blt_eq hl
    obtain ⟨ei, ci, -⟩ := csI_get (i := i + 2) (by omega)
    obtain ⟨ej, cj⟩ := cs_get (i := i + 2) (by omega)
    obtain ⟨er, cr⟩ := rep_eq hl'
    rw [(orb_enum hl').1, ei, ej, er]
    unfold conjTab
    rw [comp_pc ci cr, comp_pc (cPc ci cr) cj]
    exact notIn_of (fun _ hq => o_canon hl' hq) (cPc (cPc ci cr) cj) hn

set_option maxRecDepth 400000 in
theorem sizes_sums : ∀ U : Finset (Fin 7), 0 ∈ U → (∑ l ∈ U, hsDClassSizes.getD l 0) ∣ 360 →
    U = {0} ∨ U = Finset.univ := by
  decide +kernel

theorem basic : (∀ k < 2, permOK 3850 (hsCentTbl (k + 6)) = true ∧
      (natArr (hsCentTbl (k + 6))).size = 3850) ∧
    (∀ k < 4, permOK 3850 (hsCentTbl (k + 13)) = true ∧
      (natArr (hsCentTbl (k + 13))).size = 3850) ∧
    (∀ j < 6, ∀ i ∈ hsQWords.getD j [], i < 2) ∧ (∀ j < 2, ∀ i ∈ hsDWords.getD j [], i < 4) := by
  obtain ⟨-, c6, c7, -⟩ := CFSG.KD.LQT.HN.canons
  refine ⟨fun k hk => ⟨?_, ?_⟩, fun k hk => ⟨CFSG.KD.LQT.HN.cent_perm (by omega) (base.1 k hk),
    ?_⟩, qwords_lt, dwords_lt⟩
  · interval_cases k
    · exact CFSG.KD.LQT.HN.cent_perm (by norm_num) c6
    · exact CFSG.KD.LQT.HN.cent_perm (by norm_num) c7
  · rw [hsCentTbl_eq (by omega)]
    exact unpack_size _ _ _
  · rw [hsCentTbl_eq (by omega)]
    exact unpack_size _ _ _

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native in
open CFSG.Sporadic.SmallOddCore.Native in
theorem facts2273 : ((∀ k < 2, permOK 3850 (hsCentTbl (k + 6)) = true ∧
        (natArr (hsCentTbl (k + 6))).size = 3850) ∧
      (∀ k < 4, permOK 3850 (hsCentTbl (k + 13)) = true ∧
        (natArr (hsCentTbl (k + 13))).size = 3850) ∧
      (∀ j < 6, ∀ i ∈ hsQWords.getD j [], i < 2) ∧ (∀ j < 2, ∀ i ∈ hsDWords.getD j [], i < 4)
    )
    ∧ (enumOK 3850 hsQGens hsQEnum = true ∧ hsQEnum.tabs.size = 64 ∧
      normalOK 3850 hsQEnum.tabs hsC1Tabs hsC1Invs hsQGens = true
    )
    ∧ (enumOK 3850 hsC1Tabs hsC1Enum = true ∧ hsC1Enum.tabs.size = 7680 ∧
      (hsC1Enum.tabs.toList.filter (commAll 3850 hsQGens)).length = 4
    )
    ∧ (enumOK 3850 hsDGens hsDEnum = true ∧ hsDEnum.tabs.size = 360 ∧
      normalOK 3850 hsDEnum.tabs hsC2Tabs hsC2Invs hsDGens = true
    )
    ∧ ((∀ i < 8, ∀ j ∈ hsCosWords.getD i [], j < 4) ∧ invsOK 3850 hsCosTabs hsCosInvs = true ∧
      (∀ i < 8, ∀ j < 8, i ≠ j →
        notInOK hsDEnum.tabs (comp 3850 hsCosInvs[i]! hsCosTabs[j]!) = true) ∧
      commAll 3850 hsDGens hsCosTabs[1]! = true ∧
      (∀ i < 6, notInOK hsDOrbits[hsCosCls.getD i 0]!.tabs
        (conjTab 3850 hsCosInvs[i + 2]! hsCosTabs[i + 2]!
          (wordTabS 3850 hsDGens (hsDClassWords.getD (hsCosCls.getD i 0) []))) = true)
    )
    ∧ (hsDOrbits.size = 7 ∧ hsDGens.size = 2 ∧
      (∀ l < 7, orbitOK 3850 hsDGens hsDInvs (wordTabS 3850 hsDGens (hsDClassWords.getD l []))
        hsDOrbits[l]! = true ∧ hsDOrbits[l]!.tabs.size = hsDClassSizes.getD l 0) ∧
      (∀ l < 7, ∀ l' < 7, l ≠ l' →
        notInOK hsDOrbits[l]!.tabs (wordTabS 3850 hsDGens (hsDClassWords.getD l' [])) = true) ∧
      (∀ l < 7, ∀ j ∈ hsDClassWords.getD l [], j < hsDGens.size) ∧
      wordTabS 3850 hsDGens (hsDClassWords.getD 0 []) = idTab 3850
    )
    ∧ (coverAllOK hsDEnum.tabs hsDOrbits = true)
    ∧ (∀ U : Finset (Fin 7), 0 ∈ U → (∑ l ∈ U, hsDClassSizes.getD l 0) ∣ 360 →
      U = {0} ∨ U = Finset.univ
    ) := by
  refine ⟨basic, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, c1_filter⟩, ⟨?_, ?_, ?_⟩, cosets,
    ⟨by simp [hsDOrbits], by simp [hsDGens], fun l hl => ?_, fun l hl l' hl' hne => ?_,
      cwords_lt, rfl⟩, ?_, sizes_sums⟩
  · rw [q_enum.1]
    exact q_enum.2
  · rw [q_enum.1]
    simp only [penumRec, Array.size_ofFn]
    exact q_cnt
  · rw [q_enum.1]
    exact q_normal
  · rw [c1_enum, c1tabs_eq]
    exact CFSG.KD.LQT.HN.enum_eq.2
  · rw [c1_enum]
    simp only [penumRec, Array.size_ofFn]
    exact CFSG.KD.LQT.HN.a_parts.2.2.2
  · rw [d_enum.1]
    exact d_enum.2
  · rw [d_enum.1]
    simp only [penumRec, Array.size_ofFn]
    exact d_cnt
  · rw [d_enum.1]
    exact d_normal
  · obtain ⟨e, ht⟩ := orb_enum hl
    rw [e]
    refine ⟨?_, orb_size hl⟩
    unfold orbitOK
    rw [invsD, ht]
    rfl
  · obtain ⟨er, cr⟩ := rep_eq hl'
    rw [(orb_enum hl).1, er]
    refine notIn_of (fun _ hq => o_canon hl hq) cr ?_
    have h := allN_spec (allN_spec notin l hl) l' hl'
    have hb : Nat.beq l l' = false := by
      cases e : Nat.beq l l'
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hne
    rw [hb] at h
    exact h
  · rw [d_enum.1]
    unfold coverAllOK
    rw [allBelow_eq_true]
    intro k hk
    have hk' : k < D.cnt := by simpa [penumRec] using hk
    exact cover_at hk'

end CFSG.KD.HSL

end
