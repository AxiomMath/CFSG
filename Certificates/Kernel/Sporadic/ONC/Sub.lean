
module

public import Certificates.Kernel.Sporadic.ONC.Lines

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.ONC
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native
open CFSG.Sporadic.SmallF2.Native (labelsOf inTreeB)

noncomputable abbrev lineTT : Table := lineOfT negN (lineReps negN)

theorem line_ok : lineChecks negN (lineReps negN) lineTT = true := by
  have hL := lineT_facts
  unfold lineChecks
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine ⟨⟨?_, fun j hj => ?_⟩, fun k hk => ?_⟩
  · rw [hL.2 0 (by norm_num)]
    exact misc_parts.2.2.2.2.2.2.2.2.2.1
  · obtain ⟨h1, h2, -, -⟩ := rp_pt hj
    rw [reps_ap hj, hL.2 _ h1, h2]
    simp [h1]
  · obtain ⟨f1, f2, f3⟩ := ln_pt hk
    have hn := (neg_pt hk).1
    rw [hL.2 k hk, negN_ap hk, hL.2 _ hn, f2, reps_ap f1]
    simp only [f1, decide_true, Bool.true_and, beq_self_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact f3

noncomputable abbrev LLT : Array Table := lineLetters lettersT (lineReps negN) lineTT

theorem LL_size : LLT.size = 8 := by
  simp [LLT, lineLetters, letters_size]

theorem LL_ap {l : ℕ} (hl : l < 8) {j : ℕ} (hj : j < 122760) : ap LLT[l]! j = LLK l j := by
  have hl' : l < lettersT.size := by rw [letters_size]; exact hl
  have e : LLT[l]! = Array.ofFn (n := nLines) fun j =>
      lineTT[((lettersT[l]!)[((lineReps negN)[j.val]!).toNat]!).toNat]! := by
    rw [getElem!_pos _ l (by rw [LL_size]; exact hl)]
    simp only [LLT, lineLetters, Array.getElem_map]
    rw [getElem!_pos lettersT l hl']
  have hr := (rp_pt hj).1
  have hx : ap lettersT[l]! (r32 RP j) < 245520 := by
    rw [letters_LJ.2 l hl _ hr]
    rcases Nat.even_or_odd' l with ⟨i, rfl | rfl⟩
    · exact (inv_pt (by omega) hr).1
    · exact (inv_pt (by omega) hr).2.1
  rw [e, ap_ofFn _ hj]
  change ap lineTT (ap lettersT[l]! (ap (lineReps negN) j)) = _
  rw [reps_ap hj, lineT_facts.2 _ hx, letters_LJ.2 l hl _ hr]
  rfl

theorem lv1_eq : levelLetters lettersT chainBase 1 = (lvK LJ BJ 8 1).toArray :=
  levelLetters_eq chain_hyp 1 (by norm_num)

theorem sub_head {i : ℕ} (hi : i < 5) :
    tbfsHdK 122760 subRoots[i]! (TCNT (3 + i)) (TPTS (3 + i)) (TPOS (3 + i)) (TPAR (3 + i))
      (TLAB (3 + i)) = true := by
  interval_cases i
  · exact hd_of (i := 3) (by norm_num) (slice_all (N := TN 3) (S := 123) (by decide)
      fun s hs => hd3All s hs)
  · exact hd_of (i := 4) (by norm_num) (slice_all (N := TN 4) (S := 123) (by decide)
      fun s hs => hd4All s hs)
  · exact hd_of (i := 5) (by norm_num) (slice_all (N := TN 5) (S := 123) (by decide)
      fun s hs => hd5All s hs)
  · exact hd_of (i := 6) (by norm_num) (slice_all (N := TN 6) (S := 123) (by decide)
      fun s hs => hd6All s hs)
  · exact hd_of (i := 7) (by norm_num) (slice_all (N := TN 7) (S := 123) (by decide)
      fun s hs => hd7All s hs)

theorem sub_pts {i : ℕ} (hi : i < 5) : ∀ k < TCNT (3 + i),
    tbfsPtK 122760 (TCNT (3 + i)) (lvK LJ BJ 8 1).length LLK (lvAt LJ BJ 8 1) (TPTS (3 + i))
      (TPOS (3 + i)) (TPAR (3 + i)) (TLAB (3 + i)) (TTI (3 + i)) k = true := by
  obtain ⟨-, -, -, -, c3, c4, c5, c6, c7, -⟩ := misc_parts
  interval_cases i
  · exact tree_all (S := 1) (by rw [c3]; norm_num) fun s hs => tr3All s hs
  · exact tree_all (S := 6) (by rw [c4]; norm_num) fun s hs => tr4All s hs
  · exact tree_all (S := 59) (by rw [c5]; norm_num) fun s hs => tr5All s hs
  · exact tree_all (S := 53) (by rw [c6]; norm_num) fun s hs => tr6All s hs
  · exact tree_all (S := 7) (by rw [c7]; norm_num) fun s hs => tr7All s hs

theorem sub_tree {i : ℕ} (hi : i < 5) :
    treeBFS nLines subRoots[i]! LLT (levelLetters lettersT chainBase 1) =
        tbfsRec 122760 (TCNT (3 + i)) (TPTS (3 + i)) (TPOS (3 + i)) (TPAR (3 + i)) (TLAB (3 + i)) ∧
      treeOK nLines subRoots[i]!
        (tbfsRec 122760 (TCNT (3 + i)) (TPTS (3 + i)) (TPOS (3 + i)) (TPAR (3 + i)) (TLAB (3 + i)))
        LLT (levelLetters lettersT chainBase 1) = true := by
  rw [lv1_eq]
  refine tbfsK_sound (L := LLK) (LV := lvAt LJ BJ 8 1) (TI := TTI (3 + i))
    ⟨by simp, fun t ht => ⟨?_, ?_, fun x hx => ?_⟩⟩ (sub_head hi) (sub_pts hi)
  · rw [getElem!_eq_getD, List.toList_toArray]
    rfl
  · rw [LL_size]
    exact (mem_lvK.1 (lvAt_mem ht)).1
  · exact LL_ap (mem_lvK.1 (lvAt_mem ht)).1 hx

noncomputable abbrev subTT : Array Tree := subTreesOf LLT (levelLetters lettersT chainBase 1)

theorem subTT_size : subTT.size = 5 := by
  simp [subTT, subTreesOf, subRoots]

theorem subTT_get {i : ℕ} (hi : i < 5) : subTT[i]! =
    tbfsRec 122760 (TCNT (3 + i)) (TPTS (3 + i)) (TPOS (3 + i)) (TPAR (3 + i)) (TLAB (3 + i)) := by
  rw [getElem!_pos _ i (by rw [subTT_size]; exact hi)]
  simp only [subTT, subTreesOf, Array.getElem_map]
  rw [← getElem!_pos subRoots i (by simpa [subRoots] using hi)]
  exact (sub_tree hi).1

theorem rec_pts_ap {n cnt : ℕ} {PTS POS PAR LAB : ℕ → ℕ} {k : ℕ} (hk : k < cnt) :
    ap (tbfsRec n cnt PTS POS PAR LAB).pts k = r32 PTS k := CFSG.KS.TBfs.ap_ofFn hk

theorem rec_pos_ap {n cnt : ℕ} {PTS POS PAR LAB : ℕ → ℕ} {z : ℕ} (hz : z < n) :
    ap (tbfsRec n cnt PTS POS PAR LAB).pos z = r32 POS z := CFSG.KS.TBfs.ap_ofFn hz

theorem rec_size {n cnt : ℕ} {PTS POS PAR LAB : ℕ → ℕ} :
    (tbfsRec n cnt PTS POS PAR LAB).pts.size = cnt := by
  unfold tbfsRec
  rw [Array.size_ofFn]

theorem lb_pt {p : ℕ} (hp : p < 122760) : r32 LB p < 5 ∧ inTK (3 + r32 LB p) p = true := by
  have h := slice_all (N := 122760) (S := 123) (by norm_num) (fun s hs => lbAll s hs) p hp
  rw [strictB_eq', bAnd_iff'] at h
  refine ⟨Nat.blt_eq.mp h.1, ?_⟩
  have := h.2
  rwa [show Nat.add 3 (r32 LB p) = 3 + r32 LB p from rfl] at this

theorem lbtr0 {k : ℕ} (hk : k < TCNT 3) : r32 LB (r32 (TPTS 3) k) = 0 := by
  have hS : TCNT 3 ≤ 1000 * 1 := by rw [misc_parts.2.2.2.2.1]; norm_num
  exact Nat.eq_of_beq_eq_true (slice_all hS (fun s hs => lb0All s hs) k hk)

theorem lbtr1 {k : ℕ} (hk : k < TCNT 4) : r32 LB (r32 (TPTS 4) k) = 1 := by
  have hS : TCNT 4 ≤ 1000 * 6 := by rw [misc_parts.2.2.2.2.2.1]; norm_num
  exact Nat.eq_of_beq_eq_true (slice_all hS (fun s hs => lb1All s hs) k hk)

theorem lbtr2 {k : ℕ} (hk : k < TCNT 5) : r32 LB (r32 (TPTS 5) k) = 2 := by
  have hS : TCNT 5 ≤ 1000 * 59 := by rw [misc_parts.2.2.2.2.2.2.1]; norm_num
  exact Nat.eq_of_beq_eq_true (slice_all hS (fun s hs => lb2All s hs) k hk)

theorem lbtr3 {k : ℕ} (hk : k < TCNT 6) : r32 LB (r32 (TPTS 6) k) = 3 := by
  have hS : TCNT 6 ≤ 1000 * 53 := by rw [misc_parts.2.2.2.2.2.2.2.1]; norm_num
  exact Nat.eq_of_beq_eq_true (slice_all hS (fun s hs => lb3All s hs) k hk)

theorem lbtr4 {k : ℕ} (hk : k < TCNT 7) : r32 LB (r32 (TPTS 7) k) = 4 := by
  have hS : TCNT 7 ≤ 1000 * 7 := by rw [misc_parts.2.2.2.2.2.2.2.2.1]; norm_num
  exact Nat.eq_of_beq_eq_true (slice_all hS (fun s hs => lb4All s hs) k hk)

theorem lbtr_pt {i : ℕ} (hi : i < 5) {k : ℕ} (hk : k < TCNT (3 + i)) :
    r32 LB (r32 (TPTS (3 + i)) k) = i := by
  interval_cases i
  · exact lbtr0 hk
  · exact lbtr1 hk
  · exact lbtr2 hk
  · exact lbtr3 hk
  · exact lbtr4 hk

theorem tree_pt_lt {i : ℕ} (hi : i < 5) {k : ℕ} (hk : k < TCNT (3 + i)) :
    r32 (TPTS (3 + i)) k < 122760 :=
  (pt_spec (sub_pts hi k hk)).lt

theorem set_loop_const {D : ℕ → ℕ} {v : ℕ} : ∀ (m : ℕ) (a : Array ℕ), (∀ k < m, D k < a.size) →
    ((List.range' 0 m).foldl (fun a k => a.set! (D k) v) a).size = a.size ∧
    ∀ p < a.size, ((List.range' 0 m).foldl (fun a k => a.set! (D k) v) a)[p]! =
      if ∃ k < m, D k = p then v else a[p]!
  | 0, a, _ => ⟨rfl, fun p _ => by simp⟩
  | m + 1, a, hD => by
    obtain ⟨hs, hv⟩ := set_loop_const m a (fun k hk => hD k (by omega))
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 m).foldl (fun a k => a.set! (D k) v) a = q at hs hv
    refine ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hs], fun p hp => ?_⟩
    rw [getElem!_set!' _ _ _ _ (by rw [hs]; exact hp), hv p hp]
    by_cases e : D m = p
    · rw [if_pos e, if_pos ⟨m, by omega, e⟩]
    · rw [if_neg e]
      by_cases h : ∃ k < m, D k = p
      · obtain ⟨k, hk, hk'⟩ := h
        rw [if_pos ⟨k, hk, hk'⟩, if_pos ⟨k, by omega, hk'⟩]
      · have h' : ¬ ∃ k < m + 1, D k = p := by
          rintro ⟨k, hk, hk'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · exact h ⟨k, hk, hk'⟩
          · exact e hk'
        rw [if_neg h, if_neg h']

theorem labelsOf_eq (n : ℕ) (S : Array Tree) : labelsOf n S = (List.range' 0 S.size).foldl
    (fun labs j => (List.range' 0 S[j]!.pts.size).foldl (fun labs k => labs.set! (ap S[j]!.pts k) j)
      labs) (Array.replicate n 0) := by
  unfold labelsOf
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]

theorem mem_tree_iff {J p : ℕ} (hJ : J < 5) (hp : p < 122760) :
    (∃ k < TCNT (3 + J), r32 (TPTS (3 + J)) k = p) ↔ r32 LB p = J := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact lbtr_pt hJ hk
  · intro h
    have hin := (lb_pt hp).2
    rw [h] at hin
    unfold inTK at hin
    rw [strictB_eq', bAnd_iff'] at hin
    exact ⟨_, Nat.blt_eq.mp hin.1, Nat.eq_of_beq_eq_true hin.2⟩

theorem labs_loop : ∀ J ≤ 5,
    ((List.range' 0 J).foldl (fun labs j => (List.range' 0 subTT[j]!.pts.size).foldl
      (fun labs k => labs.set! (ap subTT[j]!.pts k) j) labs) (Array.replicate nLines 0)).size = 122760 ∧
    ∀ p < 122760, ((List.range' 0 J).foldl (fun labs j => (List.range' 0 subTT[j]!.pts.size).foldl
      (fun labs k => labs.set! (ap subTT[j]!.pts k) j) labs) (Array.replicate nLines 0))[p]! =
        if r32 LB p < J then r32 LB p else 0
  | 0, _ => ⟨by simp [nLines], fun p hp => by simp [hp]⟩
  | J + 1, hJ => by
    obtain ⟨hs, hv⟩ := labs_loop J (by omega)
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add]
    generalize (List.range' 0 J).foldl (fun labs j => (List.range' 0 subTT[j]!.pts.size).foldl
      (fun labs k => labs.set! (ap subTT[j]!.pts k) j) labs) (Array.replicate nLines 0) = q at hs hv
    have hJ5 : J < 5 := by omega
    rw [subTT_get hJ5, rec_size]
    have hD : ∀ k < TCNT (3 + J), ap (tbfsRec 122760 (TCNT (3 + J)) (TPTS (3 + J)) (TPOS (3 + J))
        (TPAR (3 + J)) (TLAB (3 + J))).pts k < q.size := fun k hk => by
      rw [rec_pts_ap hk, hs]
      exact tree_pt_lt hJ5 hk
    obtain ⟨hs', hv'⟩ := set_loop_const (v := J) (TCNT (3 + J)) q hD
    refine ⟨by rw [hs', hs], fun p hp => ?_⟩
    rw [hv' p (by rw [hs]; exact hp), hv p hp]
    have hex : (∃ k < TCNT (3 + J), ap (tbfsRec 122760 (TCNT (3 + J)) (TPTS (3 + J)) (TPOS (3 + J))
        (TPAR (3 + J)) (TLAB (3 + J))).pts k = p) ↔ r32 LB p = J := by
      rw [← mem_tree_iff hJ5 hp]
      constructor
      · rintro ⟨k, hk, e⟩
        exact ⟨k, hk, by rw [← rec_pts_ap hk]; exact e⟩
      · rintro ⟨k, hk, e⟩
        exact ⟨k, hk, by rw [rec_pts_ap hk]; exact e⟩
    by_cases h : r32 LB p = J
    · rw [if_pos (hex.2 h), if_pos (by omega), h]
    · rw [if_neg (fun h' => h (hex.1 h'))]
      by_cases h2 : r32 LB p < J
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem labs_get {p : ℕ} (hp : p < 122760) : (labelsOf nLines subTT)[p]! = r32 LB p := by
  rw [labelsOf_eq, subTT_size, (labs_loop 5 (le_refl 5)).2 p hp, if_pos (lb_pt hp).1]

theorem inTreeB_eq {i p : ℕ} (hi : i < 5) (hp : p < 122760) :
    inTreeB subTT[i]! p = inTK (3 + i) p := by
  rw [subTT_get hi]
  unfold inTreeB inTK
  rw [rec_pos_ap hp, rec_size, strictB_eq']
  by_cases h : r32 (TPOS (3 + i)) p < TCNT (3 + i)
  · rw [rec_pts_ap h, decide_eq_true h, Bool.true_and]
    have hb : Nat.blt (r32 (TPOS (3 + i)) p) (TCNT (3 + i)) = true := Nat.blt_eq.mpr h
    rw [hb]
    rfl
  · rw [decide_eq_false h, Bool.false_and]
    have hb : Nat.blt (r32 (TPOS (3 + i)) p) (TCNT (3 + i)) = false := by
      cases e : Nat.blt (r32 (TPOS (3 + i)) p) (TCNT (3 + i))
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    rw [hb]

theorem sizes_eq : (subTT.toList.map fun T => T.pts.size) = subSizes := by
  obtain ⟨-, -, -, -, c3, c4, c5, c6, c7, -⟩ := misc_parts
  apply List.ext_getElem
  · simp [subTT_size, subSizes]
  · intro i h1 h2
    have hi : i < 5 := by simpa [subTT_size] using h1
    rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos subTT i (by rw [subTT_size]; exact hi),
      subTT_get hi, rec_size]
    interval_cases i <;> simp [subSizes, c3, c4, c5, c6, c7]

theorem sub_ok : subChecks LLT (levelLetters lettersT chainBase 1) subTT (labelsOf nLines subTT) = true := by
  unfold subChecks
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    beq_iff_eq, beq_iff_eq, beq_iff_eq, beq_iff_eq, CFSG.KS.TW.allIn_iff, CFSG.KS.TW.allIn_iff]
  refine ⟨⟨⟨⟨⟨subTT_size, rfl⟩, rfl⟩, fun i hi => ?_⟩, fun p hp => ?_⟩, sizes_eq⟩
  · rw [Bool.and_eq_true, CFSG.KS.TW.allIn_iff, subTT_get hi]
    refine ⟨(sub_tree hi).2, fun k hk => ?_⟩
    rw [rec_size] at hk
    rw [rec_pts_ap hk, labs_get (tree_pt_lt hi hk), lbtr_pt hi hk, beq_self_eq_true]
  · rw [labs_get hp, Bool.and_eq_true, decide_eq_true_eq, inTreeB_eq (lb_pt hp).1 hp]
    exact lb_pt hp

end CertificateChecks.KernelSpor.ONC

end
