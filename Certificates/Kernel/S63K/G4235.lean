module

public import Certificates.Kernel.S63K.GChecks
public import Certificates.Kernel.S63K.HBindGlue
public import CFSG.Certificates.Kernel.S63K.LayRunSound
public import CFSG.Certificates.Kernel.S63K.GeoTwinSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 100000

namespace CertificateChecks.KernelS63.G4235

open CFSG.D4Hex CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63.HD CertificateChecks.KernelS63.GD

theorem beqT {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem bAndT {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  rw [MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem bltT {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  rw [Nat.blt_eq] at h
  exact h

theorem pg_zero {D n i : ℕ} (hD : D < 2 ^ (12 * n)) (hi : n ≤ i) : pg 12 (mask 12) D i = 0 := by
  have hlt : D < 2 ^ (12 * i) :=
    lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) (by omega))
  change Nat.land (D >>> (12 * i)) (mask 12) = 0
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
  rfl

theorem get_out {β : Type} [Inhabited β] {a : Array β} {i : ℕ} (h : a.size ≤ i) :
    a[i]! = default := by
  rw [getElem!_neg a i (by omega)]

theorem bnd_parts : HD.LT < 2 ^ (12 * 7371) ∧ G 0 < 2 ^ (12 * 7371) ∧ G 2 < 2 ^ (12 * 3276) ∧
    G 3 < 2 ^ (12 * 3276) ∧ G 5 < 2 ^ (12 * 3276) ∧ G 6 < 2 ^ (12 * 3276) ∧
    G 7 < 2 ^ (12 * 12) ∧ ∀ j < 8, PA j < 2 ^ (12 * 819) := by
  have h := bnd
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, MatL.allN_iff] at h
  exact h

theorem hP : ∀ i, lineTab[i]! = LTf i := by
  intro i
  by_cases hi : i < 7371
  · exact (lt_get hi).1
  · rw [get_out (a := lineTab) (i := i) (by rw [lineTab_size]; omega)]
    exact (pg_zero bnd_parts.1 (by omega)).symm

theorem pts_parts : ∀ v < 2457, LTf (3 * v) < LTf (3 * v + 1) ∧ LTf (3 * v + 1) < LTf (3 * v + 2) ∧
    LTf (3 * v + 2) < 819 := by
  have h := ptsK
  unfold ptsOKF at h
  simp only [MatL.allN_iff, Bool.and_eq_true, decide_eq_true_eq] at h
  intro v hv
  exact ⟨(h v hv).1.1, (h v hv).1.2, (h v hv).2⟩

theorem inc_parts : (∀ x < 819, ∀ k < 9, PLf (9 * x + k) < 2457 ∧
      onLineF LTf x (PLf (9 * x + k)) = true) ∧
    ∀ v < 2457, ∀ k < 3, ∃ j < 9, PLf (9 * LTf (3 * v + k) + j) = v := by
  have h := incK
  unfold incOKF at h
  simp only [MatL.allN_iff, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range, beq_iff_eq] at h
  exact ⟨fun x hx k hk => h.1 x hx k hk, fun v hv k hk => h.2 v hv k hk⟩

theorem ptL_parts : (hexPtL lineTab).size = 7371 ∧ ∀ i < 7371, (hexPtL lineTab)[i]! = PLf i := by
  have hrow := GD.rowK
  simp only [MatL.allN_iff, Nat.blt_eq] at hrow
  refine hexPtL_of (fun v hv => ?_) hrow (fun p hp j hj => ?_) (fun v hv k hk _ => ?_)
  · rw [hP, hP, hP]
    exact ⟨(pts_parts v hv).1, (pts_parts v hv).2.1⟩
  · obtain ⟨h1, h2⟩ := inc_parts.1 p hp j hj
    refine ⟨h1, ?_⟩
    unfold onLineF at h2
    simp only [Bool.or_eq_true, beq_iff_eq] at h2
    rw [hP, hP, hP]
    rcases h2 with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [hP]
    exact inc_parts.2 v hv k hk

theorem hL : ∀ i, (hexPtL lineTab)[i]! = PLf i := by
  intro i
  by_cases hi : i < 7371
  · exact ptL_parts.2 i hi
  · rw [get_out (a := hexPtL lineTab) (i := i) (by rw [ptL_parts.1]; omega)]
    exact (pg_zero bnd_parts.2.1 (by omega)).symm

theorem nb_eq : ∀ x < 3276, hexNbr lineTab (hexPtL lineTab) x = nb x :=
  fun x _ => hexNbr_eq hP hL x

theorem root_parts : tb 1 0 = 0 ∧ tb 4 0 = 819 := by
  have h := rootL
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem lay0_parts : (hexLayBFS lineTab (hexPtL lineTab) 0).1.size = 3276 ∧
    (∀ y < 3276, (hexLayBFS lineTab (hexPtL lineTab) 0).1[y]! = L0 y) ∧
    (hexLayBFS lineTab (hexPtL lineTab) 0).2.size = 3276 ∧
    ∀ y < 3276, (hexLayBFS lineTab (hexPtL lineTab) 0).2[y]! = R0 y :=
  hexLayBFS_of_K root_parts.1 (lCons_of consL0) nb_eq (beqT runL0)

theorem lay1_parts : (hexLayBFS lineTab (hexPtL lineTab) 819).1.size = 3276 ∧
    (∀ y < 3276, (hexLayBFS lineTab (hexPtL lineTab) 819).1[y]! = L1 y) ∧
    (hexLayBFS lineTab (hexPtL lineTab) 819).2.size = 3276 ∧
    ∀ y < 3276, (hexLayBFS lineTab (hexPtL lineTab) 819).2[y]! = R1 y :=
  hexLayBFS_of_K root_parts.2 (lCons_of consL1) nb_eq (beqT runL1)

theorem hY0 : ∀ y, (hexLayBFS lineTab (hexPtL lineTab) 0).1[y]! = L0 y := by
  intro y
  by_cases hy : y < 3276
  · exact lay0_parts.2.1 y hy
  · rw [get_out (a := (hexLayBFS lineTab (hexPtL lineTab) 0).1) (i := y)
      (by rw [lay0_parts.1]; omega)]
    exact (pg_zero bnd_parts.2.2.1 (by omega)).symm

theorem hR0 : ∀ y, (hexLayBFS lineTab (hexPtL lineTab) 0).2[y]! = R0 y := by
  intro y
  by_cases hy : y < 3276
  · exact lay0_parts.2.2.2 y hy
  · rw [get_out (a := (hexLayBFS lineTab (hexPtL lineTab) 0).2) (i := y)
      (by rw [lay0_parts.2.2.1]; omega)]
    exact (pg_zero bnd_parts.2.2.2.1 (by omega)).symm

theorem hY1 : ∀ y, (hexLayBFS lineTab (hexPtL lineTab) 819).1[y]! = L1 y := by
  intro y
  by_cases hy : y < 3276
  · exact lay1_parts.2.1 y hy
  · rw [get_out (a := (hexLayBFS lineTab (hexPtL lineTab) 819).1) (i := y)
      (by rw [lay1_parts.1]; omega)]
    exact (pg_zero bnd_parts.2.2.2.2.1 (by omega)).symm

theorem hR1 : ∀ y, (hexLayBFS lineTab (hexPtL lineTab) 819).2[y]! = R1 y := by
  intro y
  by_cases hy : y < 3276
  · exact lay1_parts.2.2.2 y hy
  · rw [get_out (a := (hexLayBFS lineTab (hexPtL lineTab) 819).2) (i := y)
      (by rw [lay1_parts.2.2.1]; omega)]
    exact (pg_zero bnd_parts.2.2.2.2.2.1 (by omega)).symm

theorem lay0_get : ∀ x < 819, lay0[x]! = L0 x := by
  intro x hx
  have hl := Nat.eq_of_beq_eq_true lenY
  have hy := MatL.allN_iff.1 layY x hx
  unfold lay0
  rw [getElem!_pos _ x (by simp [hx]), Array.getElem_ofFn]
  change hexAtW layBytes x 1 = _
  have e : layBytes = (String.ofList YC).toUTF8 := by
    unfold layBytes
    rw [YC_eq]
  simp only [hexAtW, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  rw [e, byte_low lowY (by omega)]
  exact beqT hy

theorem hG : ∀ j i, (permArrs[j]!)[i]! = gG j i := by
  intro j i
  unfold gG
  by_cases hj : j < 8
  · rw [if_pos hj]
    by_cases hi : i < 819
    · exact perm_get hj hi
    · have e1 : permArrs[j]! = permArr j := by
        rw [getElem!_pos permArrs j (by rw [permArrs_size]; exact hj)]
        simp [permArrs]
      rw [e1, get_out (a := permArr j) (i := i) (by rw [permArr_size]; omega)]
      exact (pg_zero (bnd_parts.2.2.2.2.2.2.2 j hj) (by omega)).symm
  · rw [if_neg hj, get_out (a := permArrs) (i := j) (by rw [permArrs_size]; omega)]
    rfl

theorem evalArr_size : ∀ w : List ℕ, (hexEvalArr permArrs w).size = 819
  | [] => by simp [hexEvalArr, idA]
  | _ :: _ => by simp [hexEvalArr, compA]

theorem evalArr_get : ∀ w : List ℕ, (∀ k ∈ w, k < 8) → ∀ x < 819,
    (hexEvalArr permArrs w)[x]! = ptW w x ∧ ptW w x < 819
  | [], _, x, hx => by
    refine ⟨?_, hx⟩
    change (idA 819)[x]! = x
    unfold idA
    rw [getElem!_pos _ x (by simp [hx]), Array.getElem_ofFn]
  | k :: w, hw, x, hx => by
    obtain ⟨h1, h2⟩ := evalArr_get w (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) x hx
    have hk := hw k List.mem_cons_self
    have e : hexEvalArr permArrs (k :: w) = compA 819 permArrs[k]! (hexEvalArr permArrs w) := rfl
    have e2 : ptW (k :: w) x = im k (ptW w x) := rfl
    rw [e, compA_get' hx, h1, perm_get hk h2, e2]
    exact ⟨rfl, (pa_get hk h2).2⟩

theorem hW {ws : List String} (hws : hexWordsOK 8 ws = true) :
    ∀ j i, ((hexWordArrs permArrs ws)[j]!)[i]! = wF ws j i := by
  intro j i
  unfold wF hexWordArrs
  by_cases hj : j < ws.length
  · rw [if_pos hj, getElem!_pos _ j (by simpa using hj)]
    simp only [List.getElem_toArray, List.getElem_map]
    have hl : ∀ k ∈ hexDecode ws[j], k < 8 := by
      unfold hexWordsOK at hws
      have := List.all_eq_true.1 hws ws[j] (List.getElem_mem hj)
      simpa using this
    by_cases hi : i < 819
    · rw [if_pos hi, (evalArr_get _ hl i hi).1, List.getD_eq_getElem _ _ hj]
    · rw [if_neg hi, get_out (a := hexEvalArr permArrs (hexDecode ws[j])) (i := i)
        (by rw [evalArr_size]; omega)]
      rfl
  · rw [if_neg hj, get_out (a := (ws.map fun s => hexEvalArr permArrs (hexDecode s)).toArray)
      (i := j) (by simp; omega)]
    rfl

theorem wsize (ws : List String) : (hexWordArrs permArrs ws).size = ws.length := by
  simp [hexWordArrs]

theorem hactG : ∀ j y x, hexActOK lineTab permArrs[j]! y x = actOKF LTf (gG j) y x :=
  fun j y x => hexActOK_eq hP (hG j) y x

theorem hactW {ws : List String} (hws : hexWordsOK 8 ws = true) :
    ∀ j y x, hexActOK lineTab (hexWordArrs permArrs ws)[j]! y x = actOKF LTf (wF ws j) y x :=
  fun j y x => hexActOK_eq hP (hW hws j) y x

theorem words_parts : hexWordsOK 8 hexHWords = true ∧ hexWordsOK 8 hexPWords = true ∧
    hexWordsOK 8 hexNWords = true ∧ hexWordsOK 8 hexTWords = true := by
  have h := wordsK
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem len_parts : hexHWords.length = 3 ∧ hexPWords.length = 72 ∧ hexNWords.length = 2 ∧
    hexTWords.length = 6 := by
  have h := lenK
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem oCons_of {N cnt : ℕ} {O Ps : ℕ → ℕ} (h : orbConsK N cnt O Ps = true) (hc : cnt ≤ N) :
    OCons O Ps N cnt := by
  unfold orbConsK at h
  obtain ⟨ha, hb⟩ := bAndT h
  rw [MatL.allN_iff] at ha hb
  refine ⟨hc, fun i hi => ?_, fun y hy => ?_⟩
  · obtain ⟨h1, h2⟩ := bAndT (ha i hi)
    exact ⟨bltT h1, beqT h2⟩
  · have h2 := hb y hy
    cases e : Nat.beq (Ps y) N with
    | true => exact Or.inl (beqT e)
    | false =>
      rw [e] at h2
      obtain ⟨h3, h4⟩ := bAndT h2
      exact Or.inr ⟨bltT h3, beqT h4⟩

theorem keys_inj : ∀ a < 2457, ∀ b < 2457, keyF LTf a = keyF LTf b → a = b :=
  (bfsDistK_sound keyK).2

theorem orb_facts {k cnt root t : ℕ} {A : Array (Array ℕ)} {g : ℕ → ℕ → ℕ}
    (hg : ∀ j i, (A[j]!)[i]! = g j i) (hcnt : 0 < cnt) (hcN : cnt ≤ 3276)
    (h0 : Ot t 0 = root) (hp0 : Pat t 0 = 0) (hl0 : Lat t 0 = 0)
    (hcons : orbConsK 3276 cnt (Ot t) (Pst t) = true)
    (hrun : orbRunK (Wt t) (Pat t) (Lat t) k (cnt + 1) 0 1 = cnt)
    (hact : orbActF LTf g k cnt (Ot t) (Wt t) = true)
    (hbO : G (9 + 5 * t) < 2 ^ (12 * cnt)) (hbP : G (10 + 5 * t) < 2 ^ (12 * cnt))
    (hbL : G (11 + 5 * t) < 2 ^ (12 * cnt)) (hbS : G (12 + 5 * t) < 2 ^ (12 * 3276)) :
    (∀ i, (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).ord[i]! = Ot t i) ∧
      (∀ i, (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).par[i]! = Pat t i) ∧
      (∀ i, (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).lab[i]! = Lat t i) ∧
      (∀ i, (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).pos[i]! = Pst t i) ∧
      (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).ord.size = cnt ∧
      (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).par.size = cnt ∧
      (orbBFS 3276 k (hexActS lineTab (hexLineKeyMap lineTab) A) root).lab.size = cnt := by
  have hC := oCons_of hcons hcN
  unfold orbActF at hact
  simp only [MatL.allN_iff, Bool.and_eq_true, decide_eq_true_eq] at hact
  have hstep : ∀ h < cnt, ∀ j < k, hexActS lineTab (hexLineKeyMap lineTab) A j (Ot t h) =
      Ot t (Wt t (k * h + j)) := fun h hh j hj =>
    hexActS_of hP keys_inj (hg j) (hact h hh j hj).2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := orbBFS_of_K hcnt h0 hp0 hl0 hC hstep hrun
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, h1, h3, h5⟩
  · by_cases hi : i < cnt
    · exact h2 i hi
    · rw [getElem!_neg _ i (by omega)]
      exact (pg_zero hbO (by omega)).symm
  · by_cases hi : i < cnt
    · exact h4 i hi
    · rw [getElem!_neg _ i (by omega)]
      exact (pg_zero hbP (by omega)).symm
  · by_cases hi : i < cnt
    · exact h6 i hi
    · rw [getElem!_neg _ i (by omega)]
      exact (pg_zero hbL (by omega)).symm
  · by_cases hi : i < 3276
    · rw [h8 i hi]
      rcases hC.p i hi with e | ⟨e, -⟩
      · rw [e, if_neg (by omega)]
      · rw [if_pos e]
    · rw [getElem!_neg _ i (by omega)]
      exact (pg_zero hbS (by omega)).symm

theorem bndO_parts : G 9 < 2 ^ (12 * 2457) ∧ G 10 < 2 ^ (12 * 2457) ∧ G 11 < 2 ^ (12 * 2457) ∧
    G 12 < 2 ^ (12 * 3276) ∧ G 14 < 2 ^ (12 * 512) ∧ G 15 < 2 ^ (12 * 512) ∧
    G 16 < 2 ^ (12 * 512) ∧ G 17 < 2 ^ (12 * 3276) ∧ G 19 < 2 ^ (12 * 768) ∧
    G 20 < 2 ^ (12 * 768) ∧ G 21 < 2 ^ (12 * 768) ∧ G 22 < 2 ^ (12 * 3276) ∧
    G 24 < 2 ^ (12 * 2048) ∧ G 25 < 2 ^ (12 * 2048) ∧ G 26 < 2 ^ (12 * 2048) ∧
    G 27 < 2 ^ (12 * 3276) := by
  have h := bndO
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Nat.blt_eq] at h
  exact h

theorem root_o (t : ℕ) (ht : t < 4) : Pat t 0 = 0 ∧ Lat t 0 = 0 := by
  have h := bAndT (MatL.allN_iff.1 rootO t ht)
  exact ⟨beqT h.1, beqT h.2⟩

theorem root_o' : Ot 0 0 = 819 ∧ Ot 1 0 = hexB0 ∧ Ot 2 0 = hexY0 ∧ Ot 3 0 = hexM0 := by
  have h := rootO'
  simp only [MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem cons_o : orbConsK 3276 2457 (Ot 0) (Pst 0) = true ∧
    orbConsK 3276 512 (Ot 1) (Pst 1) = true ∧ orbConsK 3276 768 (Ot 2) (Pst 2) = true ∧
    orbConsK 3276 2048 (Ot 3) (Pst 3) = true := by
  have h := consO
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem t1 : hexPtsOK lineTab = true := by
  rw [hexPtsOK_eq hP (by rw [lineTab_size])]
  exact ptsK

theorem t2 : hexIncOK lineTab (hexPtL lineTab) = true := by
  rw [hexIncOK_eq hP hL]
  exact incK

theorem t3 : hexMeetOK lineTab (hexPtL lineTab) = true := by
  rw [hexMeetOK_eq hP hL]
  exact meetK

theorem t4 : decide (lineTab[0]! = 0) = true := by
  rw [hP, beqT pt0K]
  rfl

theorem t7 : (allLt 819 fun x => lay0[x]! == (hexLayBFS lineTab (hexPtL lineTab) 0).1[x]!) =
    true := by
  rw [allLt_iff]
  intro x hx
  rw [lay0_get x hx, hY0]
  exact beq_self_eq_true _

theorem t8 : hexLayOK lineTab (hexPtL lineTab) 0 (hexLayBFS lineTab (hexPtL lineTab) 0).1
    (hexLayBFS lineTab (hexPtL lineTab) 0).2 = true := by
  rw [hexLayOK_eq hP hL hY0 hR0]
  exact layK0

theorem t9 : hexLayOK lineTab (hexPtL lineTab) 819 (hexLayBFS lineTab (hexPtL lineTab) 819).1
    (hexLayBFS lineTab (hexPtL lineTab) 819).2 = true := by
  rw [hexLayOK_eq hP hL hY1 hR1]
  exact layK1

theorem toArray_get (l : List ℕ) (i : ℕ) : l.toArray[i]! = l.getD i 0 := by
  by_cases hi : i < l.length
  · rw [getElem!_pos _ i (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp
  · rw [getElem!_neg _ i (by simpa using hi), List.getD_eq_default _ _ (by omega)]
    rfl

theorem t10 : hexCycleOK lineTab (hexPtL lineTab) (hexMkCycle lineTab (hexPtL lineTab) 0) =
    true := by
  have hc : hexMkCycle lineTab (hexPtL lineTab) 0 = (cycF L0 R0 nb).toArray := by
    unfold hexMkCycle cycF nb
    simp only [hY0, hR0, hexNbr_eq hP hL]
  rw [hc, hexCycleOK_eq hP hL (toArray_get _) (by simpa using beqT cycLen)]
  exact cycK

theorem t11 : hexLinesOK lineTab permArrs = true := by
  unfold hexLinesOK
  simp only [permArrs_size]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := orb_facts (k := 8) (t := 0) hG (by norm_num)
    (by norm_num) root_o'.1 (root_o 0 (by norm_num)).1 (root_o 0 (by norm_num)).2 cons_o.1
    (beqT runO0) actO0 bndO_parts.1 bndO_parts.2.1 bndO_parts.2.2.1 bndO_parts.2.2.2.1
  rw [orbOKR_eq h1 h2 h3 h4 h5 h6 h7]
  simp only [hactG]
  exact okO0

theorem ptLoc_parts : hexB0 < 819 ∧ L0 hexB0 = 6 ∧ ((List.range 9).map fun k => PLf k).Nodup ∧
    (∀ i < 3, wF hexHWords i 0 = 0) ∧
    ∀ i < 72, wF hexPWords i 0 = 0 ∧ wF hexPWords i hexB0 = hexB0 := by
  have h := ptLocK
  simp only [Bool.and_eq_true, decide_eq_true_eq, MatL.allN_iff, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem t12 : hexPtLocalOK lineTab (hexPtL lineTab) permArrs
    (hexLayBFS lineTab (hexPtL lineTab) 0).1 hexB0 hexHWords hexPWords = true := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := orb_facts (k := 3) (t := 1) (hW words_parts.1)
    (by norm_num) (by norm_num) root_o'.2.1 (root_o 1 (by norm_num)).1 (root_o 1 (by norm_num)).2
    cons_o.2.1 (beqT runO1) actO1 bndO_parts.2.2.2.2.1 bndO_parts.2.2.2.2.2.1
    bndO_parts.2.2.2.2.2.2.1 bndO_parts.2.2.2.2.2.2.2.1
  obtain ⟨p1, p2, p3, p4, p5⟩ := ptLoc_parts
  unfold hexPtLocalOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [permArrs_size, wsize, wsize, len_parts.1, len_parts.2.1]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨words_parts.1, words_parts.2.1⟩, p1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hY0]
    exact p2
  · simp only [hL]
    exact p3
  · rw [allLt_iff]
    intro i hi
    rw [hW words_parts.1, p4 i hi]
    rfl
  · rw [orbOKR_eq o1 o2 o3 o4 o5 o6 o7]
    simp only [hactW words_parts.1, hY0]
    exact okO1
  · rw [allLt_iff]
    intro i hi
    rw [hW words_parts.2.1, hW words_parts.2.1, (p5 i hi).1, (p5 i hi).2]
    simp
  · simp only [hL, hactW words_parts.2.1]
    exact ptPairK

theorem lnLoc_parts : hexY0 < 819 ∧ L1 hexY0 = 5 ∧ 819 ≤ hexM0 ∧ hexM0 < 3276 ∧ L1 hexM0 = 6 ∧
    (∀ i < 2, actOKF LTf (wF hexNWords i) 819 819 = true) ∧
    (∀ i < 6, actOKF LTf (wF hexTWords i) 819 819 = true ∧
      actOKF LTf (wF hexTWords i) hexM0 hexM0 = true) ∧
    ((List.range 3).all fun a => (List.range 3).all fun b => a == b ||
      (List.range 6).any fun i => wF hexTWords i (LTf 0) == LTf a &&
        wF hexTWords i (LTf 1) == LTf b) = true := by
  have h := lnLocK
  simp only [Bool.and_eq_true, decide_eq_true_eq, MatL.allN_iff] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2,
    h.2⟩

theorem t13 : hexLnLocalOK lineTab permArrs (hexLayBFS lineTab (hexPtL lineTab) 819).1 hexY0
    hexM0 hexNWords hexTWords = true := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := orb_facts (k := 2) (t := 2) (hW words_parts.2.2.1)
    (by norm_num) (by norm_num) root_o'.2.2.1 (root_o 2 (by norm_num)).1
    (root_o 2 (by norm_num)).2 cons_o.2.2.1 (beqT runO2) actO2 bndO_parts.2.2.2.2.2.2.2.2.1
    bndO_parts.2.2.2.2.2.2.2.2.2.1 bndO_parts.2.2.2.2.2.2.2.2.2.2.1
    bndO_parts.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := orb_facts (k := 2) (t := 3) (hW words_parts.2.2.1)
    (by norm_num) (by norm_num) root_o'.2.2.2 (root_o 3 (by norm_num)).1
    (root_o 3 (by norm_num)).2 cons_o.2.2.2 (beqT runO3) actO3
    bndO_parts.2.2.2.2.2.2.2.2.2.2.2.2.1 bndO_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    bndO_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 bndO_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := lnLoc_parts
  unfold hexLnLocalOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [permArrs_size, wsize, wsize, len_parts.2.2.1, len_parts.2.2.2]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨words_parts.2.2.1, words_parts.2.2.2⟩, p1⟩, ?_⟩, p3⟩, p4⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩
  · rw [hY1]
    exact p2
  · rw [hY1]
    exact p5
  · rw [allLt_iff]
    intro i hi
    rw [hactW words_parts.2.2.1]
    exact p6 i hi
  · rw [orbOKR_eq o1 o2 o3 o4 o5 o6 o7]
    simp only [hactW words_parts.2.2.1, hY1]
    exact okO2
  · rw [orbOKR_eq q1 q2 q3 q4 q5 q6 q7]
    simp only [hactW words_parts.2.2.1, hY1]
    exact okO3
  · rw [allLt_iff]
    intro i hi
    rw [hactW words_parts.2.2.2, hactW words_parts.2.2.2, (p7 i hi).1, (p7 i hi).2]
    rfl
  · simp only [hP, hW words_parts.2.2.2]
    exact p8

theorem c4235 : CFSG.D4Hex.d4GeoCheck CFSG.D4Hex.lineTab CFSG.D4Hex.lay0 CFSG.D4Hex.permArrs = true := by
  unfold d4GeoCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, ?_⟩, ?_⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩, t12⟩, t13⟩
  · rw [permArrs_size]
    rfl
  · rw [lay0_size]
    rfl

end CertificateChecks.KernelS63.G4235

end
