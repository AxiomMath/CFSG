module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBTwoDFixInputs

public section

namespace CertificateChecks.KernelTwoDFix

open CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2
open CFSG.Monster.VisCert.Native (actGo)

theorem actGo_acc (rows : Array ℕ) (v : ℕ) :
    ∀ n acc, actGo rows v n acc = acc ^^^ actGo rows v n 0
  | 0, acc => by simp [actGo]
  | n + 1, acc => by
    simp only [actGo]
    rw [actGo_acc rows v n, actGo_acc rows v n (if v.testBit n then 0 ^^^ rows[n]! else 0)]
    split <;> simp [Nat.xor_assoc]

theorem xor_xor_xor (a b c d : ℕ) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b, Nat.xor_comm b c, Nat.xor_assoc c, ← Nat.xor_assoc]

theorem actGo_xor (rows : Array ℕ) (a b : ℕ) :
    ∀ n, actGo rows (a ^^^ b) n 0 = actGo rows a n 0 ^^^ actGo rows b n 0
  | 0 => by simp [actGo]
  | n + 1 => by
    simp only [actGo]
    rw [actGo_acc rows (a ^^^ b) n, actGo_acc rows a n, actGo_acc rows b n, actGo_xor rows a b n,
      Nat.testBit_xor, xor_xor_xor]
    congr 1
    cases a.testBit n <;> cases b.testBit n <;> simp

theorem actGo_lt (rows : Array ℕ) (v : ℕ) (hr : ∀ i < 22, rows[i]! < 2 ^ 22) :
    ∀ n acc, n ≤ 22 → acc < 2 ^ 22 → actGo rows v n acc < 2 ^ 22
  | 0, acc, _, h => h
  | n + 1, acc, hn, h => by
    rw [actGo]
    refine actGo_lt rows v hr n _ (by omega) ?_
    split
    · exact Nat.xor_lt_two_pow h (hr n (by omega))
    · exact h

theorem actGo_eq_of_xor (ℓ : ℕ → ℕ) (hℓ : ∀ a b, ℓ (a ^^^ b) = ℓ a ^^^ ℓ b) (rows : Array ℕ)
    (v : ℕ) : ∀ n, (∀ t < n, rows[t]! = ℓ (2 ^ t)) → actGo rows v n 0 = ℓ (v % 2 ^ n)
  | 0, _ => by
    have h0 : ℓ 0 = 0 := by
      have := hℓ 0 0
      rwa [Nat.xor_self, Nat.xor_self] at this
    rw [Nat.pow_zero, Nat.mod_one, h0]
    rfl
  | n + 1, h => by
    have h0 : ℓ 0 = 0 := by
      have := hℓ 0 0
      rwa [Nat.xor_self, Nat.xor_self] at this
    have hsplit : v % 2 ^ (n + 1) = (if v.testBit n then 2 ^ n else 0) ^^^ v % 2 ^ n := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      split
      · rw [Nat.testBit_two_pow]
        rcases lt_trichotomy i n with hi | rfl | hi
        · simp [hi, Nat.ne_of_gt hi, Nat.lt_succ_of_lt hi]
        · simp_all
        · have h1 : ¬ i < n + 1 := by omega
          have h2 : ¬ i < n := by omega
          simp [Nat.ne_of_lt hi, h1, h2]
      · rw [Nat.zero_testBit, Bool.false_xor]
        rcases lt_trichotomy i n with hi | rfl | hi
        · simp [hi, Nat.lt_succ_of_lt hi]
        · simp_all
        · have h1 : ¬ i < n + 1 := by omega
          have h2 : ¬ i < n := by omega
          simp [h1, h2]
    simp only [actGo]
    rw [actGo_acc, actGo_eq_of_xor ℓ hℓ rows v n (fun t ht => h t (by omega)), hsplit, hℓ]
    congr 1
    split
    · rw [Nat.zero_xor, h n (by omega)]
    · exact h0.symm

@[expose] def vecW (w : List ℕ) (x : ℕ) : ℕ := w.foldr (fun k x => Native.actD 22 (liftRows k) x) x

theorem vecW_append (u v : List ℕ) (x : ℕ) : vecW (u ++ v) x = vecW u (vecW v x) := by
  simp [vecW, List.foldr_append]

theorem vecW_cons (k : ℕ) (w : List ℕ) (x : ℕ) :
    vecW (k :: w) x = Native.actD 22 (liftRows k) (vecW w x) := rfl

theorem wordRows_getElem (w : List ℕ) {t : ℕ} (ht : t < 22) :
    (wordRows w)[t]! = vecW w (2 ^ t) := by
  induction w with
  | nil =>
    simp only [wordRows, List.foldr_nil, Co2Inv.idRows, vecW]
    rw [getElem!_pos _ _ (by simp [ht])]
    simp [Nat.one_shiftLeft]
  | cons k w ih =>
    change (Co2Inv.rowsMul (wordRows w) (liftRows k))[t]! = _
    rw [Co2Inv.rowsMul_getElem _ _ ht, ih, vecW_cons]

theorem rowKey_eq (w : List ℕ) : rowKey w = (List.range 22).map fun t => vecW w (2 ^ t) := by
  simp only [rowKey]
  apply List.map_congr_left
  intro t ht
  exact wordRows_getElem w (List.mem_range.1 ht)

theorem vecW_xor (w : List ℕ) (a b : ℕ) : vecW w (a ^^^ b) = vecW w a ^^^ vecW w b := by
  induction w with
  | nil => rfl
  | cons k w ih => rw [vecW_cons, vecW_cons, vecW_cons, ih, Native.actD, Native.actD,
      Native.actD, actGo_xor]

@[expose] def liftsK : Bool :=
  (List.range 44).all fun k => (List.range 22).all fun t => decide ((liftRows k)[t]! < 2 ^ 22)

theorem liftRows_lt (hL : liftsK = true) (k : ℕ) {t : ℕ} (ht : t < 22) :
    (liftRows k)[t]! < 2 ^ 22 := by
  by_cases hk : k < 44
  · simp only [liftsK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hL
    exact hL k hk t ht
  · have hid : liftRows k = Co2Inv.idRows := by
      have hn : ¬ (23 ≤ k ∧ k < 44) := by omega
      simp only [liftRows, hn, ite_false]
    rw [hid, Co2Inv.idRows, getElem!_pos _ _ (by simp [ht])]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) ht

theorem vecW_lt (hL : liftsK = true) (w : List ℕ) {x : ℕ} (hx : x < 2 ^ 22) :
    vecW w x < 2 ^ 22 := by
  induction w with
  | nil => exact hx
  | cons k w ih =>
    rw [vecW_cons]
    exact actGo_lt _ _ (fun i hi => liftRows_lt hL k hi) 22 0 le_rfl (by norm_num)

theorem vecW_eq_actD (w : List ℕ) (R : Array ℕ) (hR : ∀ t < 22, R[t]! = vecW w (2 ^ t))
    {x : ℕ} (hx : x < 2 ^ 22) : vecW w x = Native.actD 22 R x := by
  rw [Native.actD, actGo_eq_of_xor (vecW w) (vecW_xor w) R x 22 hR, Nat.mod_eq_of_lt hx]

@[expose] def maskND : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: xs, acc => !acc.testBit x && maskND xs (acc ||| 2 ^ x)

theorem maskND_spec : ∀ (L : List ℕ) (acc : ℕ), maskND L acc = true →
    L.Nodup ∧ ∀ x ∈ L, acc.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: xs, acc, h => by
    simp only [maskND, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hx, hxs⟩ := maskND_spec xs _ h.2
    have hb : ∀ y ∈ xs, acc.testBit y = false ∧ y ≠ x := by
      intro y hy
      have := hxs y hy
      rw [Nat.testBit_or, Bool.or_eq_false_iff, Nat.testBit_two_pow] at this
      exact ⟨this.1, fun e => by simp [e] at this⟩
    refine ⟨List.nodup_cons.2 ⟨fun hm => (hb x hm).2 rfl, hx⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · exact (hb y hy).1

@[expose] def qK : Bool :=
  liftsK && maskND ((List.range 512).map fun m => vecW (subWord coGens m) 32) 0

theorem keyOK_rowKey (hL : liftsK = true) (w : List ℕ) : keyOK (rowKey w) = true := by
  simp only [keyOK, rowKey_eq, List.all_eq_true, List.mem_map, List.mem_range, decide_eq_true_eq]
  rintro _ ⟨t, ht, rfl⟩
  exact vecW_lt hL w (Nat.pow_lt_pow_right (by norm_num) ht)

theorem qCheck_of (h : qK = true) : qCheck = true := by
  simp only [qK, Bool.and_eq_true] at h
  obtain ⟨hL, hm⟩ := h
  have hnd := (maskND_spec _ _ hm).1
  simp only [qCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map,
    List.mem_range]
  refine ⟨?_, ?_⟩
  · refine List.Nodup.of_map (fun key => key.getD 5 0) ?_
    rw [List.map_map]
    convert hnd using 1
    apply List.map_congr_left
    intro m _
    simp [rowKey_eq]
  · rintro _ ⟨m, _, rfl⟩
    exact keyOK_rowKey hL _

@[expose] def sR : Array ℕ := #[49153, 2656501, 2086655, 3609343, 36075, 3932367, 1329190, 2917125,
  715924, 2270228, 1215000, 2048, 4096, 32768, 8192, 126976, 16384, 131072, 2097152, 3786752,
  1490944, 4100096]

@[expose] def alphaK : Bool :=
  liftsK && ((List.range 22).all fun t => sR[t]! == vecW sWord (2 ^ t)) &&
  (List.range 512).all fun m => m == 0 || m == 16 ||
    (((List.range 22).any fun t =>
      Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) != vecW (subWord coGens m) sR[t]!) &&
     ((List.range 22).any fun t =>
      Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) !=
        Native.actD 22 (liftRows 32) (vecW (subWord coGens m) sR[t]!)))

theorem map_ne_of_any {f g : ℕ → ℕ} (h : ((List.range 22).any fun t => f t != g t) = true) :
    ((List.range 22).map f == (List.range 22).map g) = false := by
  rw [List.any_eq_true] at h
  obtain ⟨t, ht, hfg⟩ := h
  rw [beq_eq_false_iff_ne]
  intro e
  have := congrArg (fun L => L.getD t 0) e
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (List.mem_range.1 ht), Option.map_some, Option.getD_some] at this
  simp [this] at hfg

theorem alphaCheck_of (h : alphaK = true) : alphaCheck = true := by
  simp only [alphaK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨hL, hS⟩, hm⟩ := h
  have hS' : ∀ t < 22, sR[t]! = vecW sWord (2 ^ t) := hS
  have ht22 : ∀ t < 22, (2 : ℕ) ^ t < 2 ^ 22 := fun t ht => Nat.pow_lt_pow_right (by norm_num) ht
  simp only [alphaCheck, List.all_eq_true, List.mem_range]
  intro m hm512
  have ha : rowKey (sWord ++ subWord coGens m) =
      (List.range 22).map fun t => Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) := by
    rw [rowKey_eq]
    apply List.map_congr_left
    intro t ht
    rw [vecW_append, vecW_eq_actD sWord sR hS' (vecW_lt hL _ (ht22 t (List.mem_range.1 ht)))]
  have hb : rowKey (subWord coGens m ++ sWord) =
      (List.range 22).map fun t => vecW (subWord coGens m) sR[t]! := by
    rw [rowKey_eq]
    apply List.map_congr_left
    intro t ht
    rw [vecW_append, hS' t (List.mem_range.1 ht)]
  have hc : rowKey ([32] ++ subWord coGens m ++ sWord) =
      (List.range 22).map fun t => Native.actD 22 (liftRows 32) (vecW (subWord coGens m) sR[t]!) := by
    rw [rowKey_eq]
    apply List.map_congr_left
    intro t ht
    rw [vecW_append, vecW_append, hS' t (List.mem_range.1 ht)]
    rfl
  simp only [keyOK_rowKey hL, Bool.true_and]
  have := hm m hm512
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at this
  rcases this with (h0 | h16) | ⟨hab, hac⟩
  · simp [h0]
  · simp [h16]
  · rw [ha, hb, hc, map_ne_of_any hab, map_ne_of_any hac]
    rfl

@[expose] def xor2 (p q : ℕ × ℕ) : ℕ × ℕ := (p.1 ^^^ q.1, p.2 ^^^ q.2)

theorem pauliVec_append (u v : List ℕ) :
    (pauliVec (u ++ v)).2 = xor2 (pauliVec u).2 (pauliVec v).2 := by
  induction u with
  | nil => simp [pauliVec, xor2]
  | cons k u ih =>
    have e : ∀ L : List ℕ, (pauliVec (k :: L)).2 = xor2 (Sp8.pauliGen k).2 (pauliVec L).2 :=
      fun L => rfl
    rw [List.cons_append, e, e, ih]
    simp only [xor2, Nat.xor_assoc]

@[expose] def pR (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 => if m.testBit n then xor2 (pR m n) (pauliBasis n).2 else pR m n

theorem pauliVec_filter (m : ℕ) : ∀ n,
    (pauliVec (((List.range n).filter fun i => m.testBit i).flatMap
      fun i => pauliWords.getD i [])).2 = pR m n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.flatMap_append, pauliVec_append,
      pauliVec_filter m n, pR]
    by_cases hb : m.testBit n
    · simp only [List.filter_cons, List.filter_nil, hb, ite_true, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, pauliBasis]
    · simp only [List.filter_cons, List.filter_nil, hb]
      simp [pauliVec, xor2]

theorem pauliProd_coords (m : ℕ) : (pauliProd m).2 = pR m 15 :=
  pauliVec_filter m 15

@[expose] def rw2 (p : ℕ × ℕ) : ℕ × ℕ := (p.1, if p.2.testBit 0 then p.2 ^^^ 191 else p.2)

theorem redW_eq (y : Model.Pauli) : redW y = rw2 y.2 := rfl

theorem rw2_xor (p q : ℕ × ℕ) : rw2 (xor2 p q) = xor2 (rw2 p) (rw2 q) := by
  simp only [rw2, xor2, Prod.mk.injEq, true_and, Nat.testBit_xor]
  cases hp : p.2.testBit 0 <;> cases hq : q.2.testBit 0 <;> simp only [Bool.xor_false,
    Bool.xor_true, Bool.not_true, Bool.not_false] <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_xor] <;>
    cases p.2.testBit i <;> cases q.2.testBit i <;> cases (191 : ℕ).testBit i <;> rfl

theorem popcN_xor : ∀ (k x y : ℕ),
    Model.popcN k (x ^^^ y) % 2 = (Model.popcN k x + Model.popcN k y) % 2
  | 0, _, _ => rfl
  | k + 1, x, y => by
    simp only [Model.popcN]
    have ih := popcN_xor k (x / 2) (y / 2)
    rw [Nat.xor_div_two, Nat.xor_mod_two_eq]
    omega

theorem parN_xor (k x y : ℕ) : Model.parN k (x ^^^ y) = (Model.parN k x ^^ Model.parN k y) := by
  have h := popcN_xor k x y
  simp only [Model.parN]
  rcases Nat.mod_two_eq_zero_or_one (Model.popcN k x) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (Model.popcN k y) with hy | hy <;>
    simp [h, Nat.add_mod, hx, hy]

theorem pairN_xor (a x y : ℕ) : Model.pairN a (x ^^^ y) = (Model.pairN a x ^^ Model.pairN a y) := by
  simp only [Model.pairN, Nat.and_xor_distrib_left, parN_xor]

@[expose] def fi (i : ℕ) (x : ℕ × ℕ) : Bool :=
  Model.pairN (duals.getD i (0, 0)).1 x.1 ^^ Model.pairN (duals.getD i (0, 0)).2 x.2

theorem fi_xor (i : ℕ) (p q : ℕ × ℕ) : fi i (xor2 p q) = (fi i p ^^ fi i q) := by
  simp only [fi, xor2, pairN_xor]
  cases Model.pairN (duals.getD i (0, 0)).1 p.1 <;> cases Model.pairN (duals.getD i (0, 0)).1 q.1 <;>
    cases Model.pairN (duals.getD i (0, 0)).2 p.2 <;>
    cases Model.pairN (duals.getD i (0, 0)).2 q.2 <;> rfl

theorem fi_zero (i : ℕ) : fi i (rw2 (0, 0)) = false := by
  simp only [rw2, Nat.zero_testBit, Bool.false_eq_true, ite_false, fi, Model.pairN, Nat.and_zero]
  rfl

@[expose] def pauliK : Bool :=
  (List.range 15).all fun j => boxed (pauliBasis j) &&
    (List.range 15).all fun i => fi i (rw2 (pauliBasis j).2) == (i == j)

theorem fi_pR (h : pauliK = true) (m : ℕ) {i : ℕ} (hi : i < 15) :
    ∀ n, n ≤ 15 → fi i (rw2 (pR m n)) = (decide (i < n) && m.testBit i)
  | 0, _ => by simp [pR, fi_zero]
  | n + 1, hn => by
    have ih := fi_pR h m hi n (by omega)
    simp only [pauliK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
    have hb := (h n (by omega)).2 i hi
    simp only [pR]
    split
    · rename_i hbit
      rw [rw2_xor, fi_xor, ih, hb]
      rcases lt_trichotomy i n with hl | rfl | hl
      · have hne : (i == n) = false := beq_eq_false_iff_ne.2 (Nat.ne_of_lt hl)
        simp [hl, Nat.lt_succ_of_lt hl, hne]
      · simp [hbit]
      · have hne : (i == n) = false := beq_eq_false_iff_ne.2 (Nat.ne_of_gt hl)
        have h1 : ¬ i < n := by omega
        have h2 : ¬ i < n + 1 := by omega
        simp [hne, h1, h2]
    · rename_i hbit
      rw [ih]
      rcases lt_trichotomy i n with hl | rfl | hl
      · simp [hl, Nat.lt_succ_of_lt hl]
      · simp [hbit]
      · have h1 : ¬ i < n := by omega
        have h2 : ¬ i < n + 1 := by omega
        simp [h1, h2]

theorem decode_fold (x : ℕ × ℕ) (m : ℕ) (h : ∀ i < 15, fi i x = m.testBit i) :
    ∀ n, n ≤ 15 → (List.range n).foldl (fun acc i => if fi i x then acc + 2 ^ i else acc) 0 =
      m % 2 ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, hn => by
    rw [List.range_succ, List.foldl_append, decode_fold x m h n (by omega), List.foldl_cons,
      List.foldl_nil, h n (by omega), Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with h2 | h2 <;> simp [h2]

theorem boxed_pR (h : pauliK = true) (m : ℕ) :
    ∀ n, n ≤ 15 → (pR m n).1 < 2 ^ 12 ∧ (pR m n).2 < 2 ^ 12
  | 0, _ => by simp [pR]
  | n + 1, hn => by
    obtain ⟨i1, i2⟩ := boxed_pR h m n (by omega)
    simp only [pauliK, List.all_eq_true, List.mem_range, Bool.and_eq_true, boxed,
      decide_eq_true_eq] at h
    obtain ⟨⟨b1, b2⟩, -⟩ := h n (by omega)
    simp only [pR]
    split
    · exact ⟨Nat.xor_lt_two_pow i1 b1, Nat.xor_lt_two_pow i2 b2⟩
    · exact ⟨i1, i2⟩

theorem pauliCheck_of (h : pauliK = true) : pauliCheck = true := by
  simp only [pauliCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  intro m hm
  have hfi : ∀ i < 15, fi i (rw2 (pR m 15)) = m.testBit i := fun i hi => by
    rw [fi_pR h m hi 15 le_rfl]
    simp [hi]
  refine ⟨?_, ?_⟩
  · have hd := decode_fold _ m hfi 15 le_rfl
    rw [Nat.mod_eq_of_lt (by simpa using hm)] at hd
    rw [redW_eq, pauliProd_coords]
    exact hd
  · obtain ⟨b1, b2⟩ := boxed_pR h m 15 le_rfl
    rw [← pauliProd_coords] at b1 b2
    simp only [boxed, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨b1, b2⟩

@[expose] def u7Mask : ℕ := u7Idx.foldl (fun a i => a ||| 2 ^ i) 0

theorem foldl_mask_testBit : ∀ (L : List ℕ) (acc x : ℕ),
    (L.foldl (fun a i => a ||| 2 ^ i) acc).testBit x = (acc.testBit x || L.contains x)
  | [], acc, x => by simp
  | y :: L, acc, x => by
    rw [List.foldl_cons, foldl_mask_testBit L, Nat.testBit_or, Nat.testBit_two_pow, List.contains_cons]
    by_cases e : y = x
    · subst e
      simp
    · have hne : (x == y) = false := beq_eq_false_iff_ne.2 (Ne.symm e)
      simp [e, hne]

theorem u7Mask_testBit (x : ℕ) : u7Mask.testBit x = u7Idx.contains x := by
  rw [u7Mask, foldl_mask_testBit]
  simp

@[expose] def betaAt (m fm : ℕ) : Bool :=
  decide (fm < 32768) && (!(u7Mask.testBit fm) || u7Mask.testBit m)

@[expose] def betaGo (rows : Array ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, m, fm => betaAt m fm
  | n + 1, m, fm => betaGo rows n m fm && betaGo rows n (m ^^^ 2 ^ n) (fm ^^^ rows[n]!)

@[expose] def betaK : Bool :=
  ((List.range 15).all fun n => Native.actD 15 commRows (2 ^ n) == commRows[n]!) &&
    betaGo commRows 15 0 0

theorem lt_of_testBit_false {x n : ℕ} (hx : x < 2 ^ (n + 1)) (hb : x.testBit n = false) :
    x < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with rfl | hi
  · exact hb
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem betaGo_spec (rows : Array ℕ)
    (hr : ∀ n < 15, Native.actD 15 rows (2 ^ n) = rows[n]!) :
    ∀ n, n ≤ 15 → ∀ m, betaGo rows n m (Native.actD 15 rows m) = true →
      ∀ lo < 2 ^ n, betaAt (m ^^^ lo) (Native.actD 15 rows (m ^^^ lo)) = true
  | 0, _, m, h, lo, hlo => by
    rw [Nat.pow_zero, Nat.lt_one_iff] at hlo
    subst hlo
    simpa only [Nat.xor_zero, betaGo] using h
  | n + 1, hn, m, h, lo, hlo => by
    simp only [betaGo, Bool.and_eq_true] at h
    by_cases hb : lo.testBit n = true
    · have hf : Native.actD 15 rows (m ^^^ 2 ^ n) = Native.actD 15 rows m ^^^ rows[n]! := by
        rw [← hr n (by omega), Native.actD, Native.actD, Native.actD, actGo_xor]
      rw [← hf] at h
      have hlo' : lo ^^^ 2 ^ n < 2 ^ n := by
        apply lt_of_testBit_false (Nat.xor_lt_two_pow hlo
          (Nat.pow_lt_pow_right (by norm_num) (by omega)))
        rw [Nat.testBit_xor, hb, Nat.testBit_two_pow_self]
        rfl
      have e : m ^^^ lo = (m ^^^ 2 ^ n) ^^^ (lo ^^^ 2 ^ n) := by
        rw [Nat.xor_assoc, ← Nat.xor_assoc (2 ^ n), Nat.xor_comm (2 ^ n) lo, Nat.xor_assoc lo,
          Nat.xor_self, Nat.xor_zero]
      rw [e]
      exact betaGo_spec rows hr n (by omega) _ h.2 _ hlo'
    · exact betaGo_spec rows hr n (by omega) m h.1 lo
        (lt_of_testBit_false hlo (by simpa using hb))

theorem betaCheck_of (h : betaK = true) : betaCheck = true := by
  simp only [betaK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hz : Native.actD 15 commRows 0 = 0 := by
    rw [Native.actD]
    clear h
    generalize 15 = n
    induction n with
    | zero => rfl
    | succ n ih => simpa [actGo] using ih
  have hs := betaGo_spec commRows h.1 15 le_rfl 0 (by rw [hz]; exact h.2)
  simp only [betaCheck, List.all_eq_true, List.mem_range]
  intro m hm
  have := hs m (by simpa using hm)
  simp only [Nat.zero_xor, betaAt, u7Mask_testBit] at this
  exact this

end CertificateChecks.KernelTwoDFix
