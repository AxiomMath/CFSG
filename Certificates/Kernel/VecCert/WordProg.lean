module

public import Certificates.Kernel.VecCert.HomBoundG
public import Certificates.Data.Kernel.Spor.WordProg
public import Certificates.Data.Kernel.Spor.WordProgW

public section

namespace CertificateChecks.KernelWP

open CFSG.KC.Ord CFSG.KC.WP CFSG.KS.Ord CertificateChecks.KernelHomG

variable {d : Nat} {K : Type} [CommRing K]

@[expose] noncomputable def wordMat (Mt : Nat → Matrix (Fin d) (Fin d) K) (RB : Nat → Nat)
    (L : Nat) (w : List Nat) : Matrix (Fin d) (Fin d) K :=
  (w.map fun c => Mt (letM RB L (letC c))).prod

@[expose] def Good (Q : Nat → Prop) (Mt : Nat → Matrix (Fin d) (Fin d) K) (RB : Nat → Nat)
    (L : Nat) (X : Nat) (w : List Nat) : Prop :=
  Q X ∧ Mt X = wordMat Mt RB L w

variable {Q : Nat → Prop} {Mt : Nat → Matrix (Fin d) (Fin d) K} {mul : Nat → Nat → Nat}
  {vld : Nat → Bool} {ONE : Nat} {RB : Nat → Nat} {L : Nat}

theorem wordMat_nil : wordMat Mt RB L [] = 1 := rfl

theorem wordMat_append (u v : List Nat) :
    wordMat Mt RB L (u ++ v) = wordMat Mt RB L u * wordMat Mt RB L v := by
  unfold wordMat
  rw [List.map_append, List.prod_append]

theorem wordMat_rep (u : List Nat) : ∀ n,
    wordMat Mt RB L (List.replicate n u).flatten = wordMat Mt RB L u ^ n
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, wordMat_append, wordMat_rep u n, pow_succ']

theorem letC_div (c : Nat) : letC c = (c / 2, decide (c % 2 = 1)) := by
  unfold letC
  have e1 : Nat.shiftRight c 1 = c / 2 := by
    change c >>> 1 = _
    rw [Nat.shiftRight_eq_div_pow]
  have e2 : Nat.land c 1 = c % 2 := by
    change c &&& 1 = _
    rw [Nat.and_one_is_mod]
  rw [e1, e2]
  congr 1

theorem letC_codeOf (x : Nat × Bool) : letC (codeOf x) = x := by
  obtain ⟨g, s⟩ := x
  rw [letC_div]
  unfold codeOf
  refine Prod.ext ?_ ?_
  · change (2 * g + bif s then 1 else 0) / 2 = g
    cases s
    · rw [Bool.cond_false]
      omega
    · rw [Bool.cond_true]
      omega
  · change decide ((2 * g + bif s then 1 else 0) % 2 = 1) = s
    cases s
    · rw [Bool.cond_false, decide_eq_false_iff_not]
      omega
    · rw [Bool.cond_true, decide_eq_true_iff]
      omega

@[expose] noncomputable def psq (mul : Nat → Nat → Nat) (ONE a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (mul a a) a (Nat.beq a ONE)

@[expose] noncomputable def pmul (mul : Nat → Nat → Nat) (ONE M : Nat) (b : Bool) (sq : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) sq
    (Bool.rec (motive := fun _ => Nat) (mul sq M) M (Nat.beq sq ONE)) b

@[expose] noncomputable def pbit (e i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def powAcc (mul : Nat → Nat → Nat) (ONE M e n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => CFSG.KC.Loop.strictN acc (fun a => pmul mul ONE M (pbit e i) (psq mul ONE a))) n

theorem powR_eq (mul : Nat → Nat → Nat) (ONE M e : Nat) :
    powR mul ONE M e = powAcc mul ONE M e (nat_lit 16) := rfl

theorem powAcc_succ (mul : Nat → Nat → Nat) (ONE M e n : Nat) :
    powAcc mul ONE M e (n + 1) = pmul mul ONE M (pbit e n) (psq mul ONE (powAcc mul ONE M e n)) := by
  have e1 : powAcc mul ONE M e (Nat.succ n) = CFSG.KC.Loop.strictN (powAcc mul ONE M e n)
      (fun a => pmul mul ONE M (pbit e n) (psq mul ONE a)) := rfl
  rw [e1]
  exact strictN_eqG _ _

theorem psq_sound (hs : LayoutSound Q Mt mul vld ONE) {a : Nat} (ha : Q a) :
    Q (psq mul ONE a) ∧ Mt (psq mul ONE a) = Mt a * Mt a := by
  unfold psq
  cases h : Nat.beq a ONE
  · exact hs.mul_sound a a ha ha
  · have e : a = ONE := Nat.eq_of_beq_eq_true h
    refine ⟨ha, ?_⟩
    change Mt a = Mt a * Mt a
    rw [e, hs.one_mt, mul_one]

theorem pmul_sound (hs : LayoutSound Q Mt mul vld ONE) {M sq : Nat} (hM : Q M) (hq : Q sq)
    (b : Bool) :
    Q (pmul mul ONE M b sq) ∧ Mt (pmul mul ONE M b sq) = Mt sq * Mt M ^ (bif b then 1 else 0) := by
  unfold pmul
  cases b
  · exact ⟨hq, by rw [Bool.cond_false, pow_zero, mul_one]⟩
  · rw [Bool.cond_true, pow_one]
    cases h : Nat.beq sq ONE
    · exact hs.mul_sound sq M hq hM
    · have e : sq = ONE := Nat.eq_of_beq_eq_true h
      refine ⟨hM, ?_⟩
      change Mt M = Mt sq * Mt M
      rw [e, hs.one_mt, one_mul]

theorem bit_mod (e j : Nat) (hj : j < 16) : e / 2 ^ j % 2 = e % 65536 / 2 ^ j % 2 := by
  have h65 : (65536 : Nat) = 2 ^ j * (2 * 2 ^ (15 - j)) := by
    interval_cases j <;> norm_num
  have h1 : 2 ^ j * (2 * (2 ^ (15 - j) * (e / 65536))) = 65536 * (e / 65536) := by
    rw [h65]
    ring
  have he : e = e % 65536 + 2 ^ j * (2 * (2 ^ (15 - j) * (e / 65536))) := by
    rw [h1]
    exact (Nat.mod_add_div e 65536).symm
  conv_lhs => rw [he]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem pbit_div (e i : Nat) (hi : i < 16) :
    e % 65536 / 2 ^ (16 - (i + 1)) = 2 * (e % 65536 / 2 ^ (16 - i)) + bif pbit e i then 1 else 0 := by
  have hj : 16 - i = (15 - i) + 1 := by omega
  have hj' : 16 - (i + 1) = 15 - i := by omega
  rw [hj, hj']
  have hjlt : 15 - i < 16 := by omega
  have hb : (bif pbit e i then 1 else 0) = e % 65536 / 2 ^ (15 - i) % 2 := by
    unfold pbit
    have hl : Nat.land (Nat.shiftRight e (Nat.sub (nat_lit 15) i)) 1 = e / 2 ^ (15 - i) % 2 := by
      change (e >>> (15 - i)) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    rw [hl, bit_mod e (15 - i) hjlt]
    rcases Nat.mod_two_eq_zero_or_one (e % 65536 / 2 ^ (15 - i)) with h | h <;> rw [h] <;> rfl
  rw [hb, pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (e % 65536 / 2 ^ (15 - i)) 2
  omega

theorem powAcc_sound (hs : LayoutSound Q Mt mul vld ONE) {M : Nat} (hM : Q M) (e : Nat) :
    ∀ n ≤ 16, Q (powAcc mul ONE M e n) ∧
      Mt (powAcc mul ONE M e n) = Mt M ^ (e % 65536 / 2 ^ (16 - n)) := by
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : e % 65536 / 2 ^ (16 - 0) = 0 :=
      Nat.div_eq_of_lt (by have := Nat.mod_lt e (show 65536 > 0 by norm_num); simpa using this)
    exact ⟨hs.one_q, by rw [h0, pow_zero]; exact hs.one_mt⟩
  | succ n ih =>
    intro hn
    obtain ⟨hq, hm⟩ := ih (by omega)
    obtain ⟨hq2, hm2⟩ := psq_sound hs hq
    obtain ⟨hq3, hm3⟩ := pmul_sound (ONE := ONE) hs hM hq2 (pbit e n)
    rw [powAcc_succ]
    refine ⟨hq3, ?_⟩
    rw [hm3, hm2, hm, pbit_div e n (by omega), pow_add, two_mul, pow_add]

theorem powR_sound (hs : LayoutSound Q Mt mul vld ONE) {M : Nat} (hM : Q M) (e : Nat) :
    Q (powR mul ONE M e) ∧ Mt (powR mul ONE M e) = Mt M ^ (e % 65536) := by
  rw [powR_eq]
  obtain ⟨h1, h2⟩ := powAcc_sound hs hM e 16 (Nat.le_refl 16)
  refine ⟨h1, ?_⟩
  rw [h2]
  norm_num

theorem strictL_eq (y : Nat) (k : Nat → List Nat) : strictL y k = k y := by
  cases y <;> rfl

theorem good_one (hs : LayoutSound Q Mt mul vld ONE) : Good Q Mt RB L ONE [] :=
  ⟨hs.one_q, hs.one_mt⟩

theorem good_mul (hs : LayoutSound Q Mt mul vld ONE) {a b : Nat} {u v : List Nat}
    (ha : Good Q Mt RB L a u) (hb : Good Q Mt RB L b v) : Good Q Mt RB L (mul a b) (u ++ v) := by
  obtain ⟨h1, h2⟩ := hs.mul_sound a b ha.1 hb.1
  exact ⟨h1, by rw [h2, ha.2, hb.2, wordMat_append]⟩

theorem good_pow (hs : LayoutSound Q Mt mul vld ONE) {a : Nat} {u : List Nat}
    (ha : Good Q Mt RB L a u) (e : Nat) :
    Good Q Mt RB L (powR mul ONE a e) (List.replicate (e % 65536) u).flatten := by
  obtain ⟨h1, h2⟩ := powR_sound hs ha.1 e
  exact ⟨h1, by rw [h2, ha.2, wordMat_rep]⟩

theorem good_let (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {c : Nat} (hc : c < 2 * L) :
    Good Q Mt RB L (letM RB L (letC c)) [c] := by
  refine ⟨letM_q hs hroot hinv ?_, ?_⟩
  · rw [letC_div]
    change c / 2 < L
    omega
  · unfold wordMat
    rw [List.map_singleton, List.prod_singleton]

theorem good_hd (hs : LayoutSound Q Mt mul vld ONE) {st : List Nat} {ws : List (List Nat)}
    (h : List.Forall₂ (Good Q Mt RB L) st ws) : Good Q Mt RB L (hdN ONE st) (hdW ws) := by
  cases h with
  | nil => exact good_one hs
  | cons h _ => exact h

theorem good_tl {st : List Nat} {ws : List (List Nat)}
    (h : List.Forall₂ (Good Q Mt RB L) st ws) : List.Forall₂ (Good Q Mt RB L) (tlN st) ws.tail := by
  cases h with
  | nil => exact List.Forall₂.nil
  | cons _ h => exact h

theorem step_sound (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {RS : Nat → Nat} {WC : Nat → List Nat} {ins : Nat}
    {st : List Nat} {ws : List (List Nat)}
    (hl : Nat.beq (Nat.land ins 3) 0 = true → Nat.shiftRight ins 2 < 2 * L)
    (hr : Nat.beq (Nat.land ins 3) 1 = true →
      Good Q Mt RB L (RS (Nat.shiftRight ins 2)) (WC (Nat.shiftRight ins 2)))
    (h : List.Forall₂ (Good Q Mt RB L) st ws) :
    List.Forall₂ (Good Q Mt RB L) (stepV RB L RS mul ONE ins st) (stepW WC ins ws) := by
  unfold stepV stepW
  dsimp only
  cases h0 : Nat.beq (Nat.land ins 3) 0
  · cases h1 : Nat.beq (Nat.land ins 3) 1
    · cases h2 : Nat.beq (Nat.land ins 3) 2
      · simp only [Bool.cond_false]
        rw [strictL_eq]
        exact List.Forall₂.cons (good_pow hs (good_hd hs h) _) (good_tl h)
      · simp only [Bool.cond_false, Bool.cond_true]
        rw [strictL_eq]
        exact List.Forall₂.cons (good_mul hs (good_hd hs (good_tl h)) (good_hd hs h))
          (good_tl (good_tl h))
    · simp only [Bool.cond_false, Bool.cond_true]
      rw [strictL_eq]
      exact List.Forall₂.cons (hr h1) h
  · simp only [Bool.cond_true]
    rw [strictL_eq]
    exact List.Forall₂.cons (good_let hs hroot hinv (hl h0)) h

theorem prog_sound (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {RS : Nat → Nat} {WC : Nat → List Nat} :
    ∀ (P : List Nat) (st : List Nat) (ws : List (List Nat)), letsOK L P = true →
      (∀ ins ∈ P, Nat.beq (Nat.land ins 3) 1 = true →
        Good Q Mt RB L (RS (Nat.shiftRight ins 2)) (WC (Nat.shiftRight ins 2))) →
      List.Forall₂ (Good Q Mt RB L) st ws →
      List.Forall₂ (Good Q Mt RB L) (progVal RB L RS mul ONE P st) (progW WC P ws)
  | [], _, _, _, _, h => h
  | ins :: P, st, ws, hP, hR, h => by
    unfold letsOK at hP
    rw [List.all_cons, Bool.and_eq_true] at hP
    have hl : Nat.beq (Nat.land ins 3) 0 = true → Nat.shiftRight ins 2 < 2 * L := by
      intro h0
      have := hP.1
      rw [h0, Bool.not_true, Bool.false_or] at this
      exact Nat.blt_eq.mp this
    exact prog_sound hs hroot hinv P _ _ hP.2 (fun i hi => hR i (List.mem_cons_of_mem _ hi))
      (step_sound hs hroot hinv hl (hR ins List.mem_cons_self) h)

theorem top_sound (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {RS : Nat → Nat} {WC : Nat → List Nat} {P : List Nat}
    (hP : letsOK L P = true)
    (hR : ∀ ins ∈ P, Nat.beq (Nat.land ins 3) 1 = true →
      Good Q Mt RB L (RS (Nat.shiftRight ins 2)) (WC (Nat.shiftRight ins 2))) :
    Good Q Mt RB L (progTop RB L RS mul ONE P) (progWord WC P) :=
  good_hd hs (prog_sound hs hroot hinv P [] [] hP hR List.Forall₂.nil)

theorem progOK_sound (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {RS : Nat → Nat} {WC : Nat → List Nat} {P : List Nat}
    {T : Nat} (h : progOK RB L RS mul ONE P T = true) (hP : letsOK L P = true)
    (hR : ∀ ins ∈ P, Nat.beq (Nat.land ins 3) 1 = true →
      Good Q Mt RB L (RS (Nat.shiftRight ins 2)) (WC (Nat.shiftRight ins 2))) :
    Good Q Mt RB L T (progWord WC P) := by
  have e : progTop RB L RS mul ONE P = T := Nat.eq_of_beq_eq_true h
  rw [← e]
  exact top_sound hs hroot hinv hP hR

theorem refs_of (k : Nat) (P : List Nat) (h : refsOK k P = true) :
    ∀ ins ∈ P, Nat.beq (Nat.land ins 3) 1 = true → Nat.shiftRight ins 2 < k := by
  intro ins hi h1
  unfold refsOK at h
  have := List.all_eq_true.mp h ins hi
  rw [h1, Bool.not_true, Bool.false_or] at this
  exact Nat.blt_eq.mp this

theorem relRange_spec {RS : Nat → Nat} {PR : Nat → List Nat} {lo : Nat} :
    ∀ n, relProgsRangeOK RB L RS mul ONE PR lo n = true →
      ∀ i < n, progOK RB L RS mul ONE (PR (lo + i)) ONE = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : andB (relProgsRangeOK RB L RS mul ONE PR lo n)
      (progOK RB L RS mul ONE (PR (Nat.add lo n)) ONE) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact relRange_spec n h1 i hi
    · exact h2

theorem stateRange_spec {RS : Nat → Nat} {PS : Nat → List Nat} {lo : Nat} :
    ∀ n, stateProgsRangeOK RB L RS mul ONE PS lo n = true →
      ∀ i < n, progOK RB L RS mul ONE (PS (lo + i)) (RS (lo + i)) = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have h' : andB (stateProgsRangeOK RB L RS mul ONE PS lo n)
      (progOK RB L RS mul ONE (PS (Nat.add lo n)) (RS (Nat.add lo n))) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact stateRange_spec n h1 i hi
    · exact h2

theorem range_join {p : Nat → Prop} {lo n m : Nat} (h1 : ∀ i < n, p (lo + i))
    (h2 : ∀ i < m, p (lo + n + i)) : ∀ i < n + m, p (lo + i) := by
  intro i hi
  by_cases h : i < n
  · exact h1 i h
  · have := h2 (i - n) (by omega)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega)] at this

theorem statesOK_spec {WC : Nat → List Nat} {PS : Nat → List Nat} :
    ∀ n, statesOK L WC PS n = true → ∀ k < n, letsOK L (PS k) = true ∧ refsOK k (PS k) = true ∧
      progWord WC (PS k) = WC k ∧ codesOK L (WC k) = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    unfold statesOK at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact statesOK_spec n h.1.1.1.1 k hk
    · exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem states_good (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {RS : Nat → Nat} {WC : Nat → List Nat}
    {PS : Nat → List Nat} {nS : Nat} (hl : statesOK L WC PS nS = true)
    (hh : ∀ k < nS, progOK RB L RS mul ONE (PS k) (RS k) = true) :
    ∀ k < nS, Good Q Mt RB L (RS k) (WC k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨h1, h2, h3, -⟩ := statesOK_spec nS hl k hk
    have hR : ∀ ins ∈ PS k, Nat.beq (Nat.land ins 3) 1 = true →
        Good Q Mt RB L (RS (Nat.shiftRight ins 2)) (WC (Nat.shiftRight ins 2)) := by
      intro ins hi h1'
      have := refs_of k (PS k) h2 ins hi h1'
      exact ih _ this (by omega)
    have := progOK_sound hs hroot hinv (hh k hk) h1 hR
    rwa [h3] at this

theorem relProgsOK_spec {nS : Nat} {PR : Nat → List Nat} :
    ∀ n, relProgsOK L nS PR n = true → ∀ j < n, letsOK L (PR j) = true ∧ refsOK nS (PR j) = true
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, h, j, hj => by
    unfold relProgsOK at h
    simp only [Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact relProgsOK_spec n h.1.1 j hj
    · exact ⟨h.1.2, h.2⟩

theorem relProgs_one (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {RS : Nat → Nat} {WC : Nat → List Nat}
    {PR : Nat → List Nat} {nS nR : Nat} (hst : ∀ k < nS, Good Q Mt RB L (RS k) (WC k))
    (hl : relProgsOK L nS PR nR = true) (hh : ∀ j < nR, progOK RB L RS mul ONE (PR j) ONE = true) :
    ∀ j < nR, wordMat Mt RB L (progWord WC (PR j)) = 1 := by
  intro j hj
  obtain ⟨h1, h2⟩ := relProgsOK_spec nR hl j hj
  have := progOK_sound hs hroot hinv (hh j hj) h1
    (fun ins hi h1' => hst _ (refs_of nS (PR j) h2 ins hi h1'))
  rw [← this.2, hs.one_mt]

theorem mem_rotC {w : List Nat} {n x : Nat} (h : x ∈ rotC w n) : x ∈ w := by
  unfold rotC at h
  rcases List.mem_append.1 h with h | h
  · exact List.mem_of_mem_drop h
  · exact List.mem_of_mem_take h

theorem mem_rotC_of {w : List Nat} {x : Nat} (h : x ∈ w) (n : Nat) : x ∈ rotC w n := by
  unfold rotC
  rw [← List.take_append_drop n w, List.mem_append] at h
  rw [List.mem_append]
  exact h.symm

theorem wordMat_rotC {w : List Nat} (h : wordMat Mt RB L w = 1) (n : Nat) :
    wordMat Mt RB L (rotC w n) = 1 := by
  unfold rotC
  rw [wordMat_append]
  rw [← List.take_append_drop n w, wordMat_append] at h
  exact mul_eq_one_comm.1 h

theorem flipC_flipC (c : Nat) : flipC (flipC c) = c := by
  unfold flipC
  omega

theorem invC_invC (w : List Nat) : invC (invC w) = w := by
  unfold invC
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro c _
  exact flipC_flipC c

theorem letC_flip (c : Nat) : letC (flipC c) = flipG (letC c) := by
  rw [letC_div, letC_div]
  unfold flipC flipG
  refine Prod.ext ?_ ?_
  · change (c + 1 - 2 * (c % 2)) / 2 = c / 2
    omega
  · change decide ((c + 1 - 2 * (c % 2)) % 2 = 1) = notB (decide (c % 2 = 1))
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · have h3 : (c + 1 - 2 * (c % 2)) % 2 = 1 := by omega
      rw [h3, h]
      all_goals rfl
    · have h3 : (c + 1 - 2 * (c % 2)) % 2 = 0 := by omega
      rw [h3, h]
      all_goals rfl

theorem wordMat_invC (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {w : List Nat} (hw : ∀ c ∈ w, c < 2 * L) :
    wordMat Mt RB L (invC w) * wordMat Mt RB L w = 1 := by
  have hpair := pair_of_invsG hs hroot hinv
  have key := prod_invG (f := fun x => Mt (letM RB L x)) (w.map letC) (by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    have hg : (letC c).1 < L := by
      rw [letC_div]
      have := hw c hc
      change c / 2 < L
      omega
    generalize letC c = x at hg ⊢
    obtain ⟨g, s⟩ := x
    cases s
    · exact hpair g hg
    · exact mul_eq_one_comm.1 (hpair g hg))
  have e1 : wordMat Mt RB L (invC w) =
      (((w.map letC).map flipG).reverse.map fun x => Mt (letM RB L x)).prod := by
    unfold wordMat invC
    simp only [List.map_reverse, List.map_map]
    apply congrArg List.prod
    apply congrArg List.reverse
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply, letC_flip]
  have e2 : wordMat Mt RB L w = ((w.map letC).map fun x => Mt (letM RB L x)).prod := by
    unfold wordMat
    rw [List.map_map]
    rfl
  rw [e1, e2]
  exact key

theorem rels_of_cover (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {rels : List (List (Nat × Bool))}
    (hb : relsBounded rels L = true) {WC : Nat → List Nat} {PR : Nat → List Nat} {nR : Nat}
    {cv : Nat → Nat} (hone : ∀ j < nR, wordMat Mt RB L (progWord WC (PR j)) = 1)
    (hcov : coverAll rels WC PR nR cv rels.length = true) :
    ∀ v ∈ rels, (v.map fun x => Mt (letM RB L x)).prod = 1 := by
  have hcov' : ∀ r < rels.length, coverOK rels WC PR nR r (cv r) = true := by
    have : ∀ n, coverAll rels WC PR nR cv n = true → ∀ r < n, coverOK rels WC PR nR r (cv r) = true := by
      intro n
      induction n with
      | zero => intro _ r hr; exact absurd hr (Nat.not_lt_zero r)
      | succ n ih =>
        intro h r hr
        unfold coverAll at h
        rw [Bool.and_eq_true] at h
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
        · exact ih h.1 r hr
        · exact h.2
    exact this _ hcov
  intro v hv
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hv
  have hc := hcov' r hr
  unfold coverOK at hc
  rw [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hj, hw⟩ := hc
  have hj' : cv r % 1024 < nR := Nat.blt_eq.mp hj
  rw [List.getD_eq_getElem _ _ hr] at hw
  have hbd : ∀ x ∈ rels[r], x.1 < L := relsBounded_spec hb _ (List.getElem_mem hr)
  have hcodes : ∀ c ∈ rels[r].map codeOf, c < 2 * L := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    have := hbd x hx
    unfold codeOf
    cases x.2 <;> simp <;> omega
  have hm : (rels[r].map fun x => Mt (letM RB L x)).prod = wordMat Mt RB L (rels[r].map codeOf) := by
    unfold wordMat
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply, letC_codeOf]
  rw [hm, hw]
  apply wordMat_rotC
  set w := progWord WC (PR (cv r % 1024)) with hwdef
  have h1 : wordMat Mt RB L w = 1 := hone _ hj'
  cases hbit : Nat.beq (cv r / 1048576) 1
  · rw [Bool.cond_false]
    exact h1
  · rw [Bool.cond_true]
    have hu : ∀ c ∈ invC w, c < 2 * L := by
      intro c hc
      apply hcodes
      rw [hw, hbit, Bool.cond_true]
      exact mem_rotC_of hc _
    have := wordMat_invC hs hroot hinv hu
    rw [invC_invC, h1, one_mul] at this
    exact this

theorem wordMat_mem {w : List Nat} (hw : ∀ c ∈ w, c < 2 * L) :
    wordMat Mt RB L w ∈ Submonoid.closure (rootSetG Mt L RB) := by
  unfold wordMat
  apply Submonoid.list_prod_mem
  intro M hM
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hM
  apply Submonoid.subset_closure
  have hc' := hw c hc
  rw [letC_div]
  by_cases h : c % 2 = 1
  · refine ⟨c / 2 + 1, by omega, by omega, ?_⟩
    rw [decide_eq_true h]
    rfl
  · refine ⟨L + 1 + c / 2, by omega, by omega, ?_⟩
    rw [decide_eq_false h]
    rfl

theorem regsIn_of (hs : LayoutSound Q Mt mul vld ONE) (hroot : rootsOK RB vld 1 (L + 1) = true)
    (hinv : invsOK RB mul vld L ONE = true) {S : Nat}
    (hst : ∀ r, 2 * L < r → r < S → ∃ w, Good Q Mt RB L (RB r) w ∧ codesOK L w = true) :
    RegsInG Q Mt L RB S := by
  intro r hr0 hrS
  by_cases hr : r ≤ 2 * L
  · refine ⟨?_, Submonoid.subset_closure ⟨r, hr0, hr, rfl⟩⟩
    by_cases hr' : r ≤ L
    · have := letM_q hs hroot hinv (x := (r - 1, true)) (by change r - 1 < L; omega)
      have e : letM RB L (r - 1, true) = RB r := by
        change RB (Nat.succ (r - 1)) = RB r
        congr 1
        omega
      rwa [e] at this
    · have := letM_q hs hroot hinv (x := (r - L - 1, false)) (by change r - L - 1 < L; omega)
      have e : letM RB L (r - L - 1, false) = RB r := by
        change RB (Nat.add (Nat.succ L) (r - L - 1)) = RB r
        congr 1
        change L + 1 + (r - L - 1) = r
        omega
      rwa [e] at this
  · obtain ⟨w, hg, hw⟩ := hst r (by omega) hrS
    refine ⟨hg.1, ?_⟩
    rw [hg.2]
    exact wordMat_mem (fun c hc => Nat.blt_eq.mp (List.all_eq_true.mp hw c hc))

end CertificateChecks.KernelWP

end
