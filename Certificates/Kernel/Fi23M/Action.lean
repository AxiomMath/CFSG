
module

public import Certificates.Kernel.Fi23K.Chain
public import Certificates.Kernel.Fi23M.SepGlue
import Certificates.Kernel.Fi23K.Card
import Certificates.Kernel.Fi23K.Misc
import Certificates.Kernel.Fi23K.OrbEq
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.PEnum CFSG.KC.Fi23K
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.Raw.Orb

theorem compT_TR23 {P Q : Table} {f g : Nat → Nat} (hP : TW.TR 31671 P f) (hQ : TW.TR 31671 Q g) :
    TW.TR 31671 (compT 31671 P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨hq1, hq2⟩ := hQ.2 i hi
  obtain ⟨hp1, hp2⟩ := hP.2 _ hq2
  refine ⟨?_, hp2⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have e : (Q[i]!).toNat = g i := hq1
  rw [e]
  exact hp1

theorem powT_TR23 {P : Table} {f : Nat → Nat} (hP : TW.TR 31671 P f) (e : Nat) :
    TW.TR 31671 (powT 31671 e P) (f^[e]) := by
  induction e with
  | zero => exact idT_TR (by norm_num)
  | succ e ih =>
    have h := compT_TR23 hP ih
    have hf : (f^[e + 1]) = fun x => f (f^[e] x) := funext fun x => Function.iterate_succ_apply' f e x
    rw [hf]
    exact h

theorem isIdT_iff23 {T : Table} {f : Nat → Nat} (hT : TW.TR 31671 T f) :
    isIdT T = true ↔ ∀ x < 31671, f x = x := by
  unfold isIdT
  rw [TW.allIn_iff]
  constructor
  · intro h x hx
    have h1 := h x hx
    rw [(hT.2 x hx).1] at h1
    simpa using h1
  · intro h x hx
    rw [(hT.2 x hx).1, h x hx]
    simp

theorem Y_TR : TW.TR 31671 (chainLetters orbLit)[2]! (wv G [54]) := letters_TR.2 2 (by norm_num)

theorem AY_TR : TW.TR 31671 (compT 31671 orbLit.alpha (chainLetters orbLit)[2]!) (wv G [39, 54]) :=
  compT_TR23 (f := tb G 39) (g := wv G [54]) (tabOf_TR (by norm_num)) Y_TR

theorem ord_y : isIdT (powT 31671 17 (chainLetters orbLit)[2]!) = true := by
  rw [isIdT_iff23 (powT_TR23 Y_TR 17)]
  intro x hx
  rw [← pow_word]
  have e1 : EL 148 = (List.replicate 17 [54]).flatten := by decide +kernel
  have e2 : ER 148 = [] := by decide +kernel
  exact eqAll (by norm_num) e1 e2 x hx

theorem ord_ay : isIdT (powT 31671 23 (compT 31671 orbLit.alpha (chainLetters orbLit)[2]!)) = true := by
  rw [isIdT_iff23 (powT_TR23 AY_TR 23)]
  intro x hx
  rw [← pow_word]
  have e1 : EL 149 = (List.replicate 23 [39, 54]).flatten := by decide +kernel
  have e2 : ER 149 = [] := by decide +kernel
  exact eqAll (by norm_num) e1 e2 x hx

theorem move_facts : LL 2 0 ≠ 0 ∧ tb G 39 (LL 2 0) ≠ 0 := by
  have h := move_ok
  unfold moveK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have h1 := h.1
    rw [e] at h1
    exact absurd h1 (by decide)
  · have h2 := h.2
    rw [e] at h2
    exact absurd h2 (by decide)

theorem ne_y : isIdT (chainLetters orbLit)[2]! = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact move_facts.1 ((isIdT_iff23 Y_TR).1 h 0 (by norm_num))

theorem ne_ay : isIdT (compT 31671 orbLit.alpha (chainLetters orbLit)[2]!) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact move_facts.2 ((isIdT_iff23 AY_TR).1 h 0 (by norm_num))

noncomputable abbrev TJ : Array CFSG.Perm.Native.Tree := trees 31671 6 CNT PTSJ POSJ PARJ LABJ

theorem cover_pt {p : Nat} (hp : p < 31671) : (p == 0 ||
    inTreeB (trK 31671 CNT PTSJ POSJ PARJ LABJ 1) p ||
      inTreeB (trK 31671 CNT PTSJ POSJ PARJ LABJ 6) p) = true := by
  have h := allN_iff.1 cover_ok p hp
  unfold inTreeB
  rw [pos_ap hp, pos_ap hp, pts_size, pts_size]
  unfold POSJ PTSJ
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h0 : p = 0
  · exact Or.inl (Or.inl h0)
  have e0 : Nat.beq p 0 = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact h0 (Nat.eq_of_beq_eq_true e)
  rw [bIf_eq, e0, if_neg Bool.false_ne_true, bIf_eq] at h
  by_cases h1 : r32 (TT 1 1) p < CNT 1 ∧ r32 (TT 1 0) (r32 (TT 1 1) p) = p
  · refine Or.inl (Or.inr ⟨h1.1, ?_⟩)
    have e := pts_ap (n := 31671) (CNT := CNT) (PTS := PTSJ) (POS := POSJ) (PAR := PARJ)
      (LAB := LABJ) h1.1
    unfold PTSJ POSJ at e
    rw [e]
    exact h1.2
  have e1 : bAnd(Nat.blt (r32 (TT 1 1) p) (CNT 1), Nat.beq (r32 (TT 1 0) (r32 (TT 1 1) p)) p) =
      false := by
    rw [Bool.eq_false_iff]
    intro e
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
    exact h1 ⟨e.1, Nat.eq_of_beq_eq_true e.2⟩
  rw [e1, if_neg Bool.false_ne_true, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
  refine Or.inr ⟨h.1, ?_⟩
  have e := pts_ap (n := 31671) (CNT := CNT) (PTS := PTSJ) (POS := POSJ) (PAR := PARJ)
    (LAB := LABJ) h.1
  unfold PTSJ POSJ at e
  rw [e]
  exact Nat.eq_of_beq_eq_true h.2

theorem beta_img : (apT orbLit.beta chainQ).toList = mapK (tb G 40) [0, 1, 2, 3, 4, 5] := by
  rw [apT_map, mapK_eq, Array.toList_map]
  apply List.map_congr_left
  intro x hx
  have hx' : x < 31671 := by
    have : x ∈ [0, 1, 2, 3, 4, 5] := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  exact ap_tabOf 40 hx'

theorem beta_img_lt : ∀ x ∈ apT orbLit.beta chainQ, x < 31671 := by
  intro x hx
  rw [apT_map] at hx
  obtain ⟨r, hr, rfl⟩ := Array.mem_map.1 hx
  have hr' : r < 31671 := by
    have : r ∈ [0, 1, 2, 3, 4, 5] := by simpa [chainQ, chainBase] using hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  have e : ap orbLit.beta r = tb G 40 r := ap_tabOf 40 hr'
  rw [e]
  exact rng 40 (by norm_num) r hr'

theorem sift_beta : Perm.Native.sift TJ (chainLetters orbLit) (chainQb ()) chainQ 0
    (apT orbLit.beta chainQ) = true := by
  rw [sift_eq chain_hyp 6 0 rfl _ beta_img_lt, beta_img]
  have h := sift_ok
  unfold siftChk siftK at h
  exact h

theorem CNT6 : CNT 6 = 28160 := by decide +kernel

theorem tree1 : (Array.ofFn (n := 6) fun i => tbfsRec 31671 (CNT i.val) (PTSJ i.val) (POSJ i.val)
    (PARJ i.val) (LABJ i.val))[1]! = trK 31671 CNT PTSJ POSJ PARJ LABJ 1 := by
  rw [getElem!_pos _ 1 (by simp), Array.getElem_ofFn]
  rfl

theorem action_ok (hcard : Hcard) (chunks : Nat) : actionChecks orbLit chunks = true := by
  have hce := (chain_eq hcard).1
  unfold actionChecks
  dsimp only
  rw [t2_eq.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, CertificateChecks.KernelFi23M.sep_ok⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, (chain_eq hcard).2 chunks⟩, ?_⟩, ?_⟩, t2_eq.2⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [orbLit_size]
    rfl
  · have eA : orbLit.alpha = tabOf 39 := rfl
    rw [eA, tabOf_size]
    rfl
  · have eB : orbLit.beta = tabOf 40 := rfl
    rw [eB, tabOf_size]
    rfl
  · unfold CFSG.Sporadic.Th.Native.invoOK
    rw [TW.allIn_iff]
    intro i hi
    have eA : orbLit.alpha = tabOf 39 := rfl
    rw [eA, ap_tabOf 39 hi, ap_tabOf 39 (rng 39 (by norm_num) i hi), (ord_pt hi).1,
      beq_self_eq_true]
  · have eB : orbLit.beta = tabOf 40 := rfl
    rw [eB]
    have h40 : TW.TR 31671 (tabOf 40) (tb G 40) := tabOf_TR (by norm_num)
    have hn : (31671 : Nat) < 2 ^ 32 := by norm_num
    exact invOK_of (f := tb G 40) (g := tb G 41) h40
      (invT_TR (f := tb G 40) (g := tb G 41) hn h40 fun i hi =>
        ⟨rng 41 (by norm_num) i hi, binv_right hi, binv_left hi⟩) fun i hi => binv_left hi
  · rw [← Array.all_toList]
    decide +kernel
  · unfold slpOK allIn
    rw [Nat.all_eq_finRange_all]
    decide +kernel
  · unfold slpPure allIn
    rw [Nat.all_eq_finRange_all]
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [hce]
    simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
      List.map_nil, Array.size_ofFn]
    decide +kernel
  · rw [hce]
    exact sift_beta
  · simp only [tbfsRec, Array.size_ofFn, CNT6]
    rfl
  · rw [hce, tree1, TW.allIn_iff]
    intro p hp
    exact cover_pt hp
  · exact ord_y
  · rw [ne_y]
    rfl
  · exact ord_ay
  · rw [ne_ay]
    rfl

end CFSG.KD.Fi23K

end
