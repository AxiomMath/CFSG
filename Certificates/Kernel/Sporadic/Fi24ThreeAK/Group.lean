module

public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Facts
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeAFacts

public section

namespace CFSG.KD.Fi24ThreeAK.Group

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.HardMathSupport.Dickson.I271.TabFi24 (aWords aE aSix q0 q1 ThreeAFacts)
open CFSG.Sporadic.Fi24 (R J JR jR cls lvl gs letters)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeAK CFSG.KS.Fi24Net CFSG.KS.Fi24Kit CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit
open CFSG.KD.Fi24ThreeO.Group (Bridge word_val eq_of_base chainBase_eq wordElt_append
  wordElt_nil wordElt_cons)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem cP_wN : ∀ (v : List ℕ), (∀ l ∈ v, l < 26) → ∀ x,
    CFSG.KS.Fi24ThreeO.cP NW NT v x = wN NW v x
  | [], _, _ => rfl
  | l :: v, hv, x => by
    change CFSG.KS.Fi24ThreeO.CF NW NT l (CFSG.KS.Fi24ThreeO.cP NW NT v x) = LN NW l (wN NW v x)
    rw [cP_wN v (fun l' h => hv l' (List.mem_cons_of_mem l h)) x]
    unfold CFSG.KS.Fi24ThreeO.CF
    rw [if_neg (by have := hv l List.mem_cons_self; omega)]

theorem wv (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) (x : Fin 306936) :
    ((wordElt w) • x).val = wN NW w x.val := by
  rw [word_val hB w hw x, cP_wN w hw]

theorem lt_app {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) :
    ∀ l ∈ u ++ v, l < 26 := by
  intro l hl
  rcases List.mem_append.1 hl with h | h
  · exact hu l h
  · exact hv l h

theorem cb_eq (t : ℕ) (ht : t < 6) :
    CFSG.Sporadic.Fi24.Native.chainBase[t]! = nthN base t := by
  rw [chainBase_eq]
  interval_cases t <;> rfl

theorem wordElt_eq (hB : Bridge) {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : ∀ b < 6, wN NW u (nthN base b) = wN NW v (nthN base b)) : wordElt u = wordElt v := by
  apply eq_of_base
  intro t ht
  apply Fin.ext
  rw [wv hB hu, wv hB hv]
  change wN NW u CFSG.Sporadic.Fi24.Native.chainBase[t]! =
    wN NW v CFSG.Sporadic.Fi24.Native.chainBase[t]!
  rw [cb_eq t ht]
  exact h t ht

theorem wordElt_eq_one (hB : Bridge) {u : List ℕ} (hu : ∀ l ∈ u, l < 26)
    (h : ∀ b < 6, wN NW u (nthN base b) = nthN base b) : wordElt u = 1 :=
  (wordElt_eq hB hu (fun _ h => absurd h List.not_mem_nil) h).trans wordElt_nil

theorem W_lt : ∀ i < 8, ∀ l ∈ W i, l < 26 := by decide

theorem aWords_eq {i : ℕ} (hi : i < 8) : aWords.getD i [] = W i := by
  interval_cases i <;> rfl

theorem aE_eq {i : ℕ} (hi : i < 8) : aE i = wordElt (W i) := by
  unfold aE
  rw [aWords_eq hi]

theorem cube_eq (w : List ℕ) : wordElt (cube w) = wordElt w ^ 3 := by
  unfold cube
  rw [wordElt_append, wordElt_append, pow_three]

theorem pow_three_of (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26)
    (h : ∀ b < 6, wN NW (cube w) (nthN base b) = nthN base b) : wordElt w ^ 3 = 1 := by
  rw [← cube_eq]
  exact wordElt_eq_one hB (lt_app hw (lt_app hw hw)) h

theorem mem_list8 {i : ℕ} (hi : i < 8) : i ∈ [0, 1, 2, 3, 4, 5, 6, 7] := by
  interval_cases i <;> simp

theorem aE_pow (hB : Bridge) {i : ℕ} (hi : i < 8) : aE i ^ 3 = 1 := by
  rw [aE_eq hi]
  exact pow_three_of hB (W_lt i hi) fun b hb => (d4_fact hb).1 i (mem_list8 hi)

theorem aE_fix (hB : Bridge) {i : ℕ} (hi : i < 8) : aE i • q0 = q0 ∧ aE i • q1 = q1 := by
  obtain ⟨h0, h1⟩ := fix_fact i (mem_list8 hi)
  rw [aE_eq hi]
  exact ⟨Fin.ext (by rw [wv hB (W_lt i hi)]; exact h0),
    Fin.ext (by rw [wv hB (W_lt i hi)]; exact h1)⟩

theorem aE_ne_one (hB : Bridge) {i : ℕ} (hi : i < 8) (h : wN NW (W i) 5604 ≠ 5604) : aE i ≠ 1 := by
  intro e
  apply h
  have := wv hB (W_lt i hi) (⟨5604, by norm_num⟩ : Fin 306936)
  rw [← aE_eq hi, e, one_smul] at this
  exact this.symm

theorem nthL_mem : ∀ (S : List (List ℕ)) (j : ℕ), j < S.length → nthL S j ∈ S
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: S, 0, _ => List.mem_cons_self
  | a :: S, j + 1, h => List.mem_cons_of_mem a (nthL_mem S j (by simpa using h))

theorem sixW_length (a b : ℕ) : (sixW W a b).length = 6 := rfl

theorem sixW_lt {a b : ℕ} (ha : a < 4) (hb : b < 4) : ∀ w ∈ sixW W a b, ∀ l ∈ w, l < 26 := by
  have xa := W_lt (2 * a) (by omega)
  have ya := W_lt (2 * a + 1) (by omega)
  have xb := W_lt (2 * b) (by omega)
  have yb := W_lt (2 * b + 1) (by omega)
  intro w hw
  simp only [sixW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact xa
  · exact ya
  · exact lt_app xa (lt_app xa (lt_app xb (lt_app xb (lt_app xa xb))))
  · exact lt_app yb (lt_app yb (lt_app ya (lt_app ya (lt_app yb ya))))
  · exact xb
  · exact yb

theorem inv_sq {g : J} (h : g ^ 3 = 1) : g⁻¹ = g * g :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact h)

theorem six_eq (hB : Bridge) {a b : ℕ} (ha : a < 4) (hb : b < 4) (i : Fin 6) :
    wordElt (nthL (sixW W a b) i.val) = aSix a b i := by
  have ex := aE_eq (i := 2 * a) (by omega)
  have ey := aE_eq (i := 2 * a + 1) (by omega)
  have ex' := aE_eq (i := 2 * b) (by omega)
  have ey' := aE_eq (i := 2 * b + 1) (by omega)
  have cx := aE_pow hB (i := 2 * a) (by omega)
  have cy := aE_pow hB (i := 2 * a + 1) (by omega)
  have cx' := aE_pow hB (i := 2 * b) (by omega)
  have cy' := aE_pow hB (i := 2 * b + 1) (by omega)
  fin_cases i
  · exact ex.symm
  · exact ey.symm
  · change wordElt (W (2 * a) ++ (W (2 * a) ++ (W (2 * b) ++ (W (2 * b) ++ (W (2 * a) ++
      W (2 * b)))))) = (aE (2 * a))⁻¹ * (aE (2 * b))⁻¹ * aE (2 * a) * aE (2 * b)
    simp only [wordElt_append]
    rw [inv_sq cx, inv_sq cx', ex, ex']
    group
  · change wordElt (W (2 * b + 1) ++ (W (2 * b + 1) ++ (W (2 * a + 1) ++ (W (2 * a + 1) ++
      (W (2 * b + 1) ++ W (2 * a + 1)))))) =
      ((aE (2 * a + 1))⁻¹ * (aE (2 * b + 1))⁻¹ * aE (2 * a + 1) * aE (2 * b + 1))⁻¹
    simp only [wordElt_append]
    rw [show ∀ p q r t : J, (p⁻¹ * q⁻¹ * r * t)⁻¹ = t⁻¹ * r⁻¹ * q * p from fun _ _ _ _ => by group,
      inv_sq cy, inv_sq cy', ey, ey']
    group
  · exact ex'.symm
  · exact ey'.symm

@[expose] def numW (w : List (Fin 6 × Bool)) : List (ℕ × Bool) := w.map fun p => (p.1.val, p.2)

theorem rels_eq : a2Words.map numW = rels := by decide

theorem relW_lt {S : List (List ℕ)} (hS : ∀ j < 6, ∀ l ∈ nthL S j, l < 26) :
    ∀ (w : List (Fin 6 × Bool)), ∀ l ∈ relW S (numW w), l < 26
  | [], l, hl => absurd hl List.not_mem_nil
  | (j, c) :: w, l, hl => by
    have hp := hS j.val j.isLt
    change l ∈ Bool.rec (motive := fun _ => List ℕ) (nthL S j.val ++ nthL S j.val)
      (nthL S j.val) c ++ relW S (numW w) at hl
    rcases List.mem_append.1 hl with h | h
    · cases c
      · exact lt_app hp hp l h
      · exact hp l h
    · exact relW_lt hS w l h

theorem evalW_eq {S : List (List ℕ)} {n : Fin 6 → J}
    (hS : ∀ j : Fin 6, wordElt (nthL S j.val) = n j) (hc : ∀ j, n j ^ 3 = 1) :
    ∀ (w : List (Fin 6 × Bool)), evalW n w = wordElt (relW S (numW w))
  | [] => by rw [evalW_nil]; rfl
  | (j, c) :: w => by
    have e2 : relW S (numW ((j, c) :: w)) = Bool.rec (motive := fun _ => List ℕ)
        (nthL S j.val ++ nthL S j.val) (nthL S j.val) c ++ relW S (numW w) := rfl
    rw [evalW_cons, e2, wordElt_append, evalW_eq hS hc w]
    dsimp only
    cases c
    · rw [if_neg (by decide), inv_sq (hc j)]
      change n j * n j * _ = wordElt (nthL S j.val ++ nthL S j.val) * _
      rw [wordElt_append, hS]
    · rw [if_pos rfl]
      change n j * _ = wordElt (nthL S j.val) * _
      rw [hS]

theorem edge_of (hB : Bridge) {a b : ℕ} (ha : a < 4) (hb : b < 4)
    (hc : ∀ bp < 6, ∀ w ∈ sixW W a b, wN NW (cube w) (nthN base bp) = nthN base bp)
    (hr : ∀ bp < 6, ∀ r ∈ rels, wN NW (relW (sixW W a b) r) (nthN base bp) = nthN base bp) :
    RelsHold (aSix a b) a2Words := by
  have hS := six_eq hB ha hb
  have hSl : ∀ j < 6, ∀ l ∈ nthL (sixW W a b) j, l < 26 := fun j hj =>
    sixW_lt ha hb _ (nthL_mem _ j (by rw [sixW_length]; exact hj))
  have hcube : ∀ i : Fin 6, aSix a b i ^ 3 = 1 := fun i => by
    rw [← hS i]
    exact pow_three_of hB (hSl i.val i.isLt) fun bp hbp =>
      hc bp hbp _ (nthL_mem _ i.val (by rw [sixW_length]; exact i.isLt))
  intro w hw
  rw [evalW_eq hS hcube w]
  refine wordElt_eq_one hB (relW_lt hSl w) fun bp hbp => hr bp hbp _ ?_
  rw [← rels_eq]
  exact List.mem_map_of_mem hw

theorem edges (hB : Bridge) : ∀ e ∈ [(0, 1), (1, 2), (1, 3)], RelsHold (aSix e.1 e.2) a2Words := by
  intro e he
  have h4 : e.1 < 4 ∧ e.2 < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  exact edge_of hB h4.1 h4.2 (fun bp hbp => ((d4_fact hbp).2.1 e he).1)
    (fun bp hbp => ((d4_fact hbp).2.1 e he).2)

theorem nodes (hB : Bridge) : ∀ e ∈ [(0, 2), (0, 3), (2, 3)], ∀ u < 2, ∀ v < 2,
    aE (2 * e.1 + u) * aE (2 * e.2 + v) = aE (2 * e.2 + v) * aE (2 * e.1 + u) := by
  intro e he u hu v hv
  have h4 : e.1 < 4 ∧ e.2 < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  have hu' : u ∈ [0, 1] := by interval_cases u <;> simp
  have hv' : v ∈ [0, 1] := by interval_cases v <;> simp
  have l1 := W_lt (2 * e.1 + u) (by omega)
  have l2 := W_lt (2 * e.2 + v) (by omega)
  rw [aE_eq (by omega), aE_eq (by omega), ← wordElt_append, ← wordElt_append]
  exact wordElt_eq hB (lt_app l1 l2) (lt_app l2 l1) fun bp hbp => (d4_fact hbp).2.2 e he u hu' v hv'

theorem OL_eq : CFSG.KD.Fi24ThreeO.OL = CFSG.KD.Fi24Orb.OL := rfl

theorem cls_val (hB : Bridge) (k p : Fin 306936) :
    (cls k • p).val = clsK CFSG.KD.Fi24Orb.OL NT k.val p.val := by
  rw [hB.cls, OL_eq]

theorem line_val (hB : Bridge) : (cls q0 • q1).val = 73618 := by
  rw [cls_val hB]
  exact line_fact

theorem noncomm (hB : Bridge) : cls q0 * cls q1 ≠ cls q1 * cls q0 := by
  intro hc
  have h := congrArg Fin.val ((smul_eq_iff_commute_R (cls q0) q1).2 hc)
  rw [line_val hB] at h
  exact absurd h (by decide)

theorem fix_of_mem_lvl_two {g : J} (hg : g ∈ lvl 2) : g • q0 = q0 ∧ g • q1 = q1 := by
  have hg1 : g ∈ lvl 1 := CFSG.Perm.levelGroup_anti _ (by norm_num : 1 ≤ 2) hg
  have e0 : idx 306936 g 0 = 0 := (CFSG.Sporadic.Fi24.lvl_one_iff g).2 hg1
  have e1 := (CFSG.Sporadic.Fi24.chain_facts'.2.1 1
    (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num) g hg1).2 hg
  rw [CFSG.Sporadic.Fi24.chainBase_one] at e1
  constructor
  · apply Fin.ext
    have := idx_of_lt g (show 0 < 306936 by norm_num)
    rw [e0] at this
    exact this.symm
  · apply Fin.ext
    have := idx_of_lt g (show 305530 < 306936 by norm_num)
    rw [e1] at this
    exact this.symm

theorem ev_mem (hlv : levelLetters letters CFSG.Sporadic.Fi24.Native.chainBase 2 =
    #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
    ∀ w : List ℕ, (∀ l ∈ w, l ∈ ev) → wordElt w ∈ lvl 2
  | [], _ => by rw [wordElt_nil]; exact (lvl 2).one_mem
  | l :: w, hw => by
    rw [wordElt_cons]
    refine (lvl 2).mul_mem (CFSG.Perm.lG_mem ?_) (ev_mem hlv w fun l' h => hw l' (List.mem_cons_of_mem l h))
    rw [hlv]
    have h := hw l List.mem_cons_self
    simp only [ev, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem conj_inv {G : Type*} [Group G] {h s k : G} (hs : h * s * h⁻¹ = s) (hk : k * s * k = s⁻¹) :
    (h * k * h⁻¹) * s * (h * k * h⁻¹) = s⁻¹ := by
  calc h * k * h⁻¹ * s * (h * k * h⁻¹) = h * k * (h⁻¹ * s * h) * k * h⁻¹ := by group
    _ = h * (k * s * k) * h⁻¹ := by
      rw [show h⁻¹ * s * h = s by
        calc h⁻¹ * s * h = h⁻¹ * (h * s * h⁻¹) * h := by rw [hs]
          _ = s := by group]
      group
    _ = h * s⁻¹ * h⁻¹ := by rw [hk]
    _ = (h * s * h⁻¹)⁻¹ := by group
    _ = s⁻¹ := by rw [hs]

theorem reps_mem {x : ℕ} (h : x ∈ reps) : ∃ i < 5, nthN reps i = x := by
  simp only [reps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
    ⟨3, by norm_num, rfl⟩, ⟨4, by norm_num, rfl⟩]

theorem tests_lt {i : ℕ} (hi : i < 5) : nthN tests i < 306936 := by
  interval_cases i <;> decide

theorem scan_of (hB : Bridge) (hlv : levelLetters letters CFSG.Sporadic.Fi24.Native.chainBase 2 =
    #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) (k : Fin 306936)
    (hk : cls k * (cls q0 * cls q1) * cls k = (cls q0 * cls q1)⁻¹) :
    k = q0 ∨ k = q1 ∨ k = cls q0 • q1 := by
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨h0, h1, h2⟩ := hne
  have hk0 : k.val ≠ 0 := fun e => h0 (Fin.ext e)
  have hk1 : k.val ≠ 73618 := fun e => h2 (Fin.ext (by rw [e, line_val hB]))
  have hk2 : k.val ≠ 305530 := fun e => h1 (Fin.ext e)
  obtain ⟨w, hw, hr⟩ := cover_fact k.isLt hk0 hk1 hk2
  have hwl : ∀ l ∈ w, l < 26 := fun l hl => ev_lt l (hw l hl)
  set g := wordElt w with hg
  obtain ⟨f0, f1⟩ := fix_of_mem_lvl_two (ev_mem hlv w hw)
  have c0 : jR g * cls q0 * (jR g)⁻¹ = cls q0 := by rw [← CFSG.Sporadic.Fi24.cls_smul, f0]
  have c1 : jR g * cls q1 * (jR g)⁻¹ = cls q1 := by rw [← CFSG.Sporadic.Fi24.cls_smul, f1]
  have cs : jR g * (cls q0 * cls q1) * (jR g)⁻¹ = cls q0 * cls q1 := by
    calc jR g * (cls q0 * cls q1) * (jR g)⁻¹ =
        (jR g * cls q0 * (jR g)⁻¹) * (jR g * cls q1 * (jR g)⁻¹) := by group
      _ = cls q0 * cls q1 := by rw [c0, c1]
  have hinv := conj_inv (G := R) cs hk
  rw [← CFSG.Sporadic.Fi24.cls_smul] at hinv
  obtain ⟨i, hi, hri⟩ := reps_mem hr
  have hrv : (g • k).val = nthN reps i := by rw [hri, hg, wv hB hwl]
  set q : Fin 306936 := ⟨nthN tests i, tests_lt hi⟩
  have hq : ((cls (g • k) * (cls q0 * cls q1) * cls (g • k)) • q).val =
      ((cls q0 * cls q1)⁻¹ • q).val := by rw [hinv]
  have hs0 : (cls q0)⁻¹ = cls q0 := inv_eq_of_mul_eq_one_right (cls_mul_self q0)
  have hs1 : (cls q1)⁻¹ = cls q1 := inv_eq_of_mul_eq_one_right (cls_mul_self q1)
  rw [mul_inv_rev, hs0, hs1] at hq
  simp only [mul_smul] at hq
  rw [cls_val hB, cls_val hB, cls_val hB, cls_val hB, cls_val hB, cls_val hB, hrv] at hq
  apply fail_fact i hi
  unfold sK sKi
  rw [CFSG.KS.Fi24NetPt.strictN_eq, CFSG.KS.Fi24NetPt.strictN_eq]
  exact hq

theorem cW_lt : ∀ l ∈ cW, l < 26 := by decide

theorem conj_of (hB : Bridge) : ∃ g : J, jR (g * wordElt [18] * g⁻¹) = cls q0 * cls q1 := by
  obtain ⟨s, hs⟩ := exists_jR_of_mem (cls_mul_cls_mem_JR q0 q1)
  refine ⟨wordElt cW, ?_⟩
  have e : wordElt cW * wordElt [18] = s * wordElt cW := by
    apply eq_of_base
    intro t ht
    apply Fin.ext
    rw [← wordElt_append, wv hB (lt_app cW_lt (by decide)), mul_smul,
      ← CFSG.Sporadic.Fi24.jR_smul s, hs, mul_smul, cls_val hB, cls_val hB, wv hB cW_lt]
    change wN NW (cW ++ [18]) CFSG.Sporadic.Fi24.Native.chainBase[t]! =
      clsK CFSG.KD.Fi24Orb.OL NT 0 (clsK CFSG.KD.Fi24Orb.OL NT 305530
        (wN NW cW CFSG.Sporadic.Fi24.Native.chainBase[t]!))
    rw [cb_eq t ht, conj_fact ht]
    unfold sK
    rw [CFSG.KS.Fi24NetPt.strictN_eq]
  rw [e, mul_inv_cancel_right, hs]

theorem threeAFacts_of (hB : Bridge) (hlv : levelLetters letters
    CFSG.Sporadic.Fi24.Native.chainBase 2 =
    #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) : ThreeAFacts :=
  ⟨noncomm hB, scan_of hB hlv, conj_of hB, fun i hi => ⟨aE_pow hB hi, aE_fix hB hi⟩,
    aE_ne_one hB (by norm_num) moves_fact.1, aE_ne_one hB (by norm_num) moves_fact.2, edges hB,
    nodes hB⟩

end CFSG.KD.Fi24ThreeAK.Group

end
