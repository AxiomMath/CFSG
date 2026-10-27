module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheck
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

namespace CertificateChecks.KernelCSide

open CFSG.EvenSporadicStandard.HNRecog.CSide

def code (x : F4) : ℕ := x.a.val + 2 * x.b.val

theorem code_lt : ∀ x : F4, code x < 4 := by decide

noncomputable def mulF (x y : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight 2625168384 (Nat.add (Nat.shiftLeft x 3) (Nat.shiftLeft y 1))) 3

noncomputable def frF (x : ℕ) : ℕ := Nat.xor x (Nat.shiftRight x 1)

def dF (k : ℕ) : F4 := ⟨((Nat.land k 1 : ℕ) : ZMod 2), ((Nat.land (Nat.shiftRight k 1) 1 : ℕ) : ZMod 2)⟩

theorem code_mul : ∀ x y : F4, code (x * y) = mulF (code x) (code y) := by decide +kernel
theorem code_add : ∀ x y : F4, code (x + y) = Nat.xor (code x) (code y) := by decide +kernel
theorem code_frob : ∀ x : F4, code (F4.frob x) = frF (code x) := by decide +kernel
theorem code_inj : ∀ x y : F4, code x = code y → x = y := by decide +kernel
theorem code_b : ∀ x : F4, x.b.val = Nat.shiftRight (code x) 1 := by decide +kernel
theorem code_dFF : ∀ k : Fin 4, code (dF k) = k := by decide +kernel

theorem code_dF (k : ℕ) (hk : k < 4) : code (dF k) = k := code_dFF ⟨k, hk⟩
theorem code_zero : code 0 = 0 := by decide +kernel
theorem code_one : code 1 = 1 := by decide +kernel

noncomputable def f0 (m : ℕ) : ℕ := Nat.land m 3
noncomputable def f1 (m : ℕ) : ℕ := Nat.land (Nat.shiftRight m 2) 3
noncomputable def f2 (m : ℕ) : ℕ := Nat.land (Nat.shiftRight m 4) 3
noncomputable def f3 (m : ℕ) : ℕ := Nat.land (Nat.shiftRight m 6) 3

noncomputable def pk (a b c d : ℕ) : ℕ :=
  Nat.lor a (Nat.lor (Nat.shiftLeft b 2) (Nat.lor (Nat.shiftLeft c 4) (Nat.shiftLeft d 6)))

theorem fldF : ∀ a b c d : Fin 4,
    f0 (pk a b c d) = a ∧ f1 (pk a b c d) = b ∧ f2 (pk a b c d) = c ∧ f3 (pk a b c d) = d ∧
      pk a b c d < 256 := by decide +kernel

theorem fld (a : ℕ) (ha : a < 4) (b : ℕ) (hb : b < 4) (c : ℕ) (hc : c < 4) (d : ℕ) (hd : d < 4) :
    f0 (pk a b c d) = a ∧ f1 (pk a b c d) = b ∧ f2 (pk a b c d) = c ∧ f3 (pk a b c d) = d ∧
      pk a b c d < 256 :=
  fldF ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩

theorem pk_fF : ∀ n : Fin 256, pk (f0 n) (f1 n) (f2 n) (f3 n) = n ∧ f0 n < 4 ∧ f1 n < 4 ∧
    f2 n < 4 ∧ f3 n < 4 := by decide +kernel

theorem pk_f (n : ℕ) (hn : n < 256) : pk (f0 n) (f1 n) (f2 n) (f3 n) = n ∧ f0 n < 4 ∧ f1 n < 4 ∧
    f2 n < 4 ∧ f3 n < 4 :=
  pk_fF ⟨n, hn⟩

noncomputable def cV (M : V0) : ℕ := pk (code (M 0 0)) (code (M 0 1)) (code (M 1 0)) (code (M 1 1))

theorem fld_cV (M : V0) : f0 (cV M) = code (M 0 0) ∧ f1 (cV M) = code (M 0 1) ∧
    f2 (cV M) = code (M 1 0) ∧ f3 (cV M) = code (M 1 1) ∧ cV M < 256 :=
  fld _ (code_lt _) _ (code_lt _) _ (code_lt _) _ (code_lt _)

theorem f0_cV (M : V0) : f0 (cV M) = code (M 0 0) := (fld_cV M).1
theorem f1_cV (M : V0) : f1 (cV M) = code (M 0 1) := (fld_cV M).2.1
theorem f2_cV (M : V0) : f2 (cV M) = code (M 1 0) := (fld_cV M).2.2.1
theorem f3_cV (M : V0) : f3 (cV M) = code (M 1 1) := (fld_cV M).2.2.2.1
theorem cV_lt (M : V0) : cV M < 256 := (fld_cV M).2.2.2.2

theorem cV_inj {M N : V0} (h : cV M = cV N) : M = N := by
  have h0 := code_inj _ _ ((f0_cV M).symm.trans ((congrArg f0 h).trans (f0_cV N)))
  have h1 := code_inj _ _ ((f1_cV M).symm.trans ((congrArg f1 h).trans (f1_cV N)))
  have h2 := code_inj _ _ ((f2_cV M).symm.trans ((congrArg f2 h).trans (f2_cV N)))
  have h3 := code_inj _ _ ((f3_cV M).symm.trans ((congrArg f3 h).trans (f3_cV N)))
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  exacts [h0, h1, h2, h3]

theorem cV_surj (n : ℕ) (hn : n < 256) : ∃ M : V0, cV M = n := by
  obtain ⟨hp, h0, h1, h2, h3⟩ := pk_f n hn
  refine ⟨Matrix.of ![![dF (f0 n), dF (f1 n)], ![dF (f2 n), dF (f3 n)]], ?_⟩
  simp only [cV, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [code_dF _ h0, code_dF _ h1, code_dF _ h2, code_dF _ h3, hp]

theorem cV_zero : cV (0 : V0) = 0 := by
  simp only [cV, Matrix.zero_apply, code_zero]
  decide +kernel

theorem cV_one : cV (1 : V0) = 65 := by
  simp only [cV, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), code_zero, code_one]
  decide +kernel

noncomputable def mulK (m n : ℕ) : ℕ :=
  pk (Nat.xor (mulF (f0 m) (f0 n)) (mulF (f1 m) (f2 n)))
    (Nat.xor (mulF (f0 m) (f1 n)) (mulF (f1 m) (f3 n)))
    (Nat.xor (mulF (f2 m) (f0 n)) (mulF (f3 m) (f2 n)))
    (Nat.xor (mulF (f2 m) (f1 n)) (mulF (f3 m) (f3 n)))

noncomputable def trK (m : ℕ) : ℕ := pk (f0 m) (f2 m) (f1 m) (f3 m)

noncomputable def frK (m : ℕ) : ℕ := pk (frF (f0 m)) (frF (f1 m)) (frF (f2 m)) (frF (f3 m))

noncomputable def detK (m : ℕ) : ℕ := Nat.xor (mulF (f0 m) (f3 m)) (mulF (f1 m) (f2 m))

noncomputable def qK (m : ℕ) : ℕ := Nat.shiftRight (detK m) 1

noncomputable def polK (m n : ℕ) : ℕ :=
  Nat.shiftRight (Nat.xor (Nat.xor (Nat.xor (mulF (f0 m) (f3 n)) (mulF (f0 n) (f3 m)))
    (mulF (f1 m) (f2 n))) (mulF (f1 n) (f2 m))) 1

noncomputable def p5h (m m2 : ℕ) : ℕ := mulK (mulK m2 m2) m

noncomputable def p5K (m : ℕ) : ℕ := p5h m (mulK m m)

theorem cV_mul (A B : V0) : cV (A * B) = mulK (cV A) (cV B) := by
  simp only [mulK, f0_cV, f1_cV, f2_cV, f3_cV]
  simp only [cV, Matrix.mul_apply, Fin.sum_univ_two, code_add, code_mul]

theorem cV_tr (A : V0) : cV A.transpose = trK (cV A) := by
  simp only [trK, f0_cV, f1_cV, f2_cV, f3_cV]
  simp only [cV, Matrix.transpose_apply]

theorem cV_map (A : V0) : cV (A.map F4.frob) = frK (cV A) := by
  simp only [frK, f0_cV, f1_cV, f2_cV, f3_cV]
  simp only [cV, Matrix.map_apply, code_frob]

theorem code_det (A : V0) : code (det0 A) = detK (cV A) := by
  simp only [detK, f0_cV, f1_cV, f2_cV, f3_cV, det0, code_add, code_mul]

theorem q0_val (M : V0) : (q0Fun M).val = qK (cV M) := by
  rw [q0Fun, code_b, code_det, qK]

theorem pol_val (M N : V0) : (q0Polar M N).val = polK (cV M) (cV N) := by
  rw [q0Polar, code_b]
  simp only [polK, f0_cV, f1_cV, f2_cV, f3_cV, code_add, code_mul]

noncomputable def allL (f : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => Bool.rec false r (f a)) L

noncomputable def anyL (f : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Bool.rec r true (f a)) L

noncomputable def lenK (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun _ _ r => Nat.succ r) L

noncomputable def filtL (f : ℕ → Bool) (k : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [] (fun n r => Bool.rec r (n :: r) (f n)) k

noncomputable def anyB (f : ℕ → Bool) (k : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun n r => Bool.rec r true (f n)) k

noncomputable def allR (f : ℕ → Bool) (lo k : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i r => Bool.rec false r (f (Nat.add lo i))) k

theorem allL_iff (f : ℕ → Bool) (L : List ℕ) : allL f L = true ↔ ∀ a ∈ L, f a = true := by
  induction L with
  | nil => exact ⟨fun _ a ha => absurd ha List.not_mem_nil, fun _ => rfl⟩
  | cons a L ih =>
    change (Bool.rec false (allL f L) (f a) : Bool) = true ↔ _
    cases h : f a
    · refine ⟨fun h' => absurd h' Bool.false_ne_true, fun h' => ?_⟩
      have h2 := h' a (List.mem_cons.2 (Or.inl rfl))
      rw [h] at h2
      exact absurd h2 Bool.false_ne_true
    · rw [ih]
      constructor
      · intro h' b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact h
        · exact h' b hb
      · exact fun h' b hb => h' b (List.mem_cons.2 (Or.inr hb))

theorem anyL_iff (f : ℕ → Bool) (L : List ℕ) : anyL f L = true ↔ ∃ a ∈ L, f a = true := by
  induction L with
  | nil => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, ha, _⟩ => absurd ha List.not_mem_nil⟩
  | cons a L ih =>
    change (Bool.rec (anyL f L) true (f a) : Bool) = true ↔ _
    cases h : f a
    · rw [ih]
      constructor
      · rintro ⟨b, hb, hf⟩
        exact ⟨b, List.mem_cons.2 (Or.inr hb), hf⟩
      · rintro ⟨b, hb, hf⟩
        rcases List.mem_cons.1 hb with rfl | hb
        · rw [h] at hf
          exact absurd hf Bool.false_ne_true
        · exact ⟨b, hb, hf⟩
    · exact ⟨fun _ => ⟨a, List.mem_cons.2 (Or.inl rfl), h⟩, fun _ => rfl⟩

theorem lenK_eq (L : List ℕ) : lenK L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg Nat.succ ih

theorem mem_filtL {f : ℕ → Bool} {k n : ℕ} : n ∈ filtL f k ↔ n < k ∧ f n = true := by
  induction k with
  | zero => exact ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h.1 (Nat.not_lt_zero _)⟩
  | succ k ih =>
    change n ∈ (Bool.rec (filtL f k) (k :: filtL f k) (f k) : List ℕ) ↔ _
    cases h : f k
    · rw [ih]
      constructor
      · exact fun h' => ⟨by omega, h'.2⟩
      · intro h'
        refine ⟨?_, h'.2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h'.1 with h1 | rfl
        · exact h1
        · rw [h] at h'
          exact absurd h'.2 Bool.false_ne_true
    · rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | h')
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, h'.2⟩
      · intro h'
        rcases Nat.lt_succ_iff_lt_or_eq.1 h'.1 with h1 | rfl
        · exact Or.inr ⟨h1, h'.2⟩
        · exact Or.inl rfl

theorem nodup_filtL (f : ℕ → Bool) (k : ℕ) : (filtL f k).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
    change (Bool.rec (filtL f k) (k :: filtL f k) (f k) : List ℕ).Nodup
    cases f k
    · exact ih
    · exact List.nodup_cons.2 ⟨fun hk => absurd (mem_filtL.1 hk).1 (Nat.lt_irrefl k), ih⟩

theorem anyB_iff (f : ℕ → Bool) (k : ℕ) : anyB f k = true ↔ ∃ n < k, f n = true := by
  induction k with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, hn, _⟩ => absurd hn (Nat.not_lt_zero _)⟩
  | succ k ih =>
    change (Bool.rec (anyB f k) true (f k) : Bool) = true ↔ _
    cases h : f k
    · rw [ih]
      constructor
      · exact fun ⟨n, hn, hf⟩ => ⟨n, by omega, hf⟩
      · rintro ⟨n, hn, hf⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h1 | rfl
        · exact ⟨n, h1, hf⟩
        · rw [h] at hf
          exact absurd hf Bool.false_ne_true
    · exact ⟨fun _ => ⟨k, by omega, h⟩, fun _ => rfl⟩

theorem allR_sound (f : ℕ → Bool) (lo k : ℕ) (h : allR f lo k = true) :
    ∀ i < k, f (lo + i) = true := by
  induction k with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    change (Bool.rec false (allR f lo k) (f (Nat.add lo k)) : Bool) = true at h
    intro i hi
    cases hk : f (Nat.add lo k)
    · rw [hk] at h
      exact absurd h Bool.false_ne_true
    · rw [hk] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | rfl
      · exact ih h i h1
      · exact hk

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

noncomputable def fixT (c1 t2 n : ℕ) : Bool := Nat.beq (mulK (mulK c1 n) t2) n

noncomputable def fixL (c1 c2 : ℕ) : List ℕ := filtL (fixT c1 (trK c2)) 256

noncomputable def zeroL (L : List ℕ) : Bool := allL (fun n => Nat.beq n 0) L

noncomputable def nondegL (L : List ℕ) : Bool :=
  allL (fun n => Bool.rec (anyL (fun m => Nat.beq (polK n m) 1) L) true (Nat.beq n 0)) L

noncomputable def plP (n m : ℕ) : Bool :=
  !Nat.beq n 0 && !Nat.beq m 0 && !Nat.beq n m && Nat.beq (qK n) 0 && Nat.beq (qK m) 0 &&
    Nat.beq (polK n m) 0

noncomputable def planeL (L : List ℕ) : Bool := anyL (fun n => anyL (plP n) L) L

noncomputable def good5L (L : List ℕ) : Bool :=
  Nat.beq (lenK L) 16 && nondegL L && !planeL L

noncomputable def swK (c1 c2 : ℕ) : Bool :=
  anyB (fun x => Nat.beq (detK x) 1 && Nat.beq (mulK x (frK c2)) (mulK c1 x)) 256

noncomputable def swapK (c1 c2 : ℕ) : Bool := swK c1 c2 && swK c2 c1

noncomputable def condK (c1 c2 : ℕ) : Bool :=
  Nat.beq (p5K c1) 65 && Nat.beq (p5K c2) 65 && !Nat.beq c1 65 && !Nat.beq c2 65

noncomputable def B5K (c1 c2 : ℕ) : Bool :=
  Bool.rec true (Bool.rec (good5L (fixL c1 c2)) (zeroL (fixL c1 c2)) (swapK c1 c2)) (condK c1 c2)

noncomputable def sl2L : List ℕ := filtL (fun n => Nat.beq (detK n) 1) 256

noncomputable def rowK (a : ℕ) : Bool := Bool.rec true (allL (B5K a) sl2L) (Nat.beq (detK a) 1)

local notation "⟪" x "⟫" => cV ((x : SL2) : Matrix (Fin 2) (Fin 2) F4)

theorem det_one (x : SL2) : detK ⟪x⟫ = 1 := by
  rw [← code_det, det0_eq, Matrix.SpecialLinearGroup.det_coe, code_one]

theorem eqS {x y : SL2} (h : ⟪x⟫ = ⟪y⟫) : x = y := Subtype.ext (cV_inj h)

theorem p5_of (x : SL2) (h : x ^ 5 = 1) : p5K ⟪x⟫ = 65 := by
  have hA : ((x : Matrix (Fin 2) (Fin 2) F4)) ^ 5 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  have e : ((x : Matrix (Fin 2) (Fin 2) F4)) ^ 5 =
      (x : Matrix (Fin 2) (Fin 2) F4) * x * ((x : Matrix (Fin 2) (Fin 2) F4) * x) * x := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e] at hA
  have h2 := congrArg cV hA
  simp only [cV_mul, cV_one] at h2
  exact h2

theorem ne_of (x : SL2) (h : x ≠ 1) : ⟪x⟫ ≠ 65 := fun h' =>
  h (eqS (h'.trans (cV_one.symm.trans (congrArg cV Matrix.SpecialLinearGroup.coe_one.symm))))

theorem cond_of (g : SL2 × SL2) (h5 : g ^ 5 = 1) (h1 : g.1 ≠ 1) (h2 : g.2 ≠ 1) :
    condK ⟪g.1⟫ ⟪g.2⟫ = true := by
  have e1 : g.1 ^ 5 = 1 := by rw [← Prod.pow_fst, h5, Prod.fst_one]
  have e2 : g.2 ^ 5 = 1 := by rw [← Prod.pow_snd, h5, Prod.snd_one]
  unfold condK
  rw [p5_of _ e1, p5_of _ e2, beq_false (ne_of _ h1), beq_false (ne_of _ h2)]
  rfl

theorem key1 (x y : SL2) : ⟪x * frobSL y⟫ = mulK ⟪x⟫ (frK ⟪y⟫) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, cV_mul, coe_frobSL, cV_map]

theorem key2 (x y : SL2) : ⟪x * y⟫ = mulK ⟪x⟫ ⟪y⟫ := by
  rw [Matrix.SpecialLinearGroup.coe_mul, cV_mul]

theorem swK_iff (g1 g2 : SL2) : swK ⟪g1⟫ ⟪g2⟫ = true ↔ ∃ x : SL2, x * frobSL g2 = g1 * x := by
  unfold swK
  rw [anyB_iff]
  constructor
  · rintro ⟨n, hn, hf⟩
    rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at hf
    obtain ⟨M, rfl⟩ := cV_surj n hn
    have hd : M.det = 1 := by
      rw [← det0_eq]
      apply code_inj
      rw [code_det, hf.1, code_one]
    exact ⟨⟨M, hd⟩, eqS ((key1 ⟨M, hd⟩ g2).trans (hf.2.trans (key2 g1 ⟨M, hd⟩).symm))⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟪x⟫, cV_lt _, ?_⟩
    rw [Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq, det_one, ← key1, ← key2, hx]
    exact ⟨rfl, rfl⟩

theorem swap_iff (g : SL2 × SL2) : swapK ⟪g.1⟫ ⟪g.2⟫ = true ↔ cSideSwapCent g := by
  rw [swapK, Bool.and_eq_true, swK_iff, swK_iff]
  rfl

theorem fix_mem (g : SL2 × SL2) (M : V0) : cV M ∈ fixL ⟪g.1⟫ ⟪g.2⟫ ↔ M ∈ cSideFix g := by
  have e : cV (actFun g M) = mulK (mulK ⟪g.1⟫ (cV M)) (trK ⟪g.2⟫) := by
    rw [actFun, cV_mul, cV_mul, cV_tr]
  rw [fixL, mem_filtL, fixT, Nat.beq_eq, ← e]
  simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => cV_inj h.2, fun h => ⟨cV_lt M, congrArg cV h⟩⟩

theorem zero_sound (g : SL2 × SL2) (h : zeroL (fixL ⟪g.1⟫ ⟪g.2⟫) = true) :
    ∀ M ∈ cSideFix g, M = 0 := by
  intro M hM
  have h1 := (allL_iff _ _).1 h _ ((fix_mem g M).2 hM)
  simp only [Nat.beq_eq] at h1
  exact cV_inj (h1.trans cV_zero.symm)

noncomputable def cVe : V0 ↪ ℕ := ⟨cV, fun _ _ h => cV_inj h⟩

theorem card_sound (g : SL2 × SL2) (h : lenK (fixL ⟪g.1⟫ ⟪g.2⟫) = 16) :
    (cSideFix g).card = 16 := by
  have hmap : (cSideFix g).map cVe = (fixL ⟪g.1⟫ ⟪g.2⟫).toFinset := by
    ext n
    rw [Finset.mem_map, List.mem_toFinset]
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (fix_mem g M).2 hM
    · intro hn
      obtain ⟨M, rfl⟩ := cV_surj n (mem_filtL.1 hn).1
      exact ⟨M, (fix_mem g M).1 hn, rfl⟩
  have hnd : (fixL ⟪g.1⟫ ⟪g.2⟫).Nodup := nodup_filtL _ _
  rw [← Finset.card_map cVe, hmap, List.toFinset_card_of_nodup hnd, ← lenK_eq]
  exact h

theorem nondeg_sound (g : SL2 × SL2) (h : nondegL (fixL ⟪g.1⟫ ⟪g.2⟫) = true) :
    cSideNondegAt g := by
  intro M hM hM0
  have h1 := (allL_iff _ _).1 h _ ((fix_mem g M).2 hM)
  have hne : Nat.beq (cV M) 0 = false := beq_false fun h0 => hM0 (cV_inj (h0.trans cV_zero.symm))
  have h2 : anyL (fun m => Nat.beq (polK (cV M) m) 1) (fixL ⟪g.1⟫ ⟪g.2⟫) = true := by
    rw [hne] at h1
    exact h1
  obtain ⟨m, hm, hp⟩ := (anyL_iff _ _).1 h2
  simp only [Nat.beq_eq] at hp
  obtain ⟨N, rfl⟩ := cV_surj m (mem_filtL.1 hm).1
  refine ⟨N, (fix_mem g N).1 hm, fun h0 => ?_⟩
  have h3 := pol_val M N
  rw [h0, hp, ZMod.val_zero] at h3
  exact absurd h3 (by decide)

theorem plane_sound (g : SL2 × SL2) (h : planeL (fixL ⟪g.1⟫ ⟪g.2⟫) = false) :
    ¬ cSidePlaneAt g := by
  rintro ⟨M, hM, N, hN, hM0, hN0, hMN, hqM, hqN, hP⟩
  have hp : plP (cV M) (cV N) = true := by
    unfold plP
    rw [beq_false fun h0 => hM0 (cV_inj (h0.trans cV_zero.symm)),
      beq_false fun h0 => hN0 (cV_inj (h0.trans cV_zero.symm)),
      beq_false fun h0 => hMN (cV_inj h0), ← q0_val, ← q0_val, ← pol_val, hqM, hqN, hP]
    rfl
  have h1 : planeL (fixL ⟪g.1⟫ ⟪g.2⟫) = true :=
    (anyL_iff _ _).2 ⟨cV M, (fix_mem g M).2 hM, (anyL_iff _ _).2 ⟨cV N, (fix_mem g N).2 hN, hp⟩⟩
  exact Bool.false_ne_true (h.symm.trans h1)

theorem good_sound (g : SL2 × SL2) (h : good5L (fixL ⟪g.1⟫ ⟪g.2⟫) = true) :
    (cSideFix g).card = 16 ∧ cSideNondegAt g ∧ ¬ cSidePlaneAt g := by
  unfold good5L at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true'] at h
  exact ⟨card_sound g h.1.1, nondeg_sound g h.1.2, plane_sound g h.2⟩

theorem B5_sound (g : SL2 × SL2) (h : B5K ⟪g.1⟫ ⟪g.2⟫ = true) : cSideB5 g = true := by
  rw [cSideB5_iff]
  intro h5 h1 h2
  have h' : (Bool.rec (good5L (fixL ⟪g.1⟫ ⟪g.2⟫)) (zeroL (fixL ⟪g.1⟫ ⟪g.2⟫))
      (swapK ⟪g.1⟫ ⟪g.2⟫) : Bool) = true := by
    rw [B5K, cond_of g h5 h1 h2] at h
    exact h
  constructor
  · intro hs
    rw [(swap_iff g).2 hs] at h'
    exact zero_sound g h'
  · intro hs
    have hf : swapK ⟪g.1⟫ ⟪g.2⟫ = false := by
      cases hb : swapK ⟪g.1⟫ ⟪g.2⟫
      · rfl
      · exact absurd ((swap_iff g).1 hb) hs
    rw [hf] at h'
    exact good_sound g h'

theorem ch0 : allR rowK (16 * 0) 16 = true := by quickRfl
theorem ch1 : allR rowK (16 * 1) 16 = true := by quickRfl
theorem ch2 : allR rowK (16 * 2) 16 = true := by quickRfl
theorem ch3 : allR rowK (16 * 3) 16 = true := by quickRfl
theorem ch4 : allR rowK (16 * 4) 16 = true := by quickRfl
theorem ch5 : allR rowK (16 * 5) 16 = true := by quickRfl
theorem ch6 : allR rowK (16 * 6) 16 = true := by quickRfl
theorem ch7 : allR rowK (16 * 7) 16 = true := by quickRfl
theorem ch8 : allR rowK (16 * 8) 16 = true := by quickRfl
theorem ch9 : allR rowK (16 * 9) 16 = true := by quickRfl
theorem ch10 : allR rowK (16 * 10) 16 = true := by quickRfl
theorem ch11 : allR rowK (16 * 11) 16 = true := by quickRfl
theorem ch12 : allR rowK (16 * 12) 16 = true := by quickRfl
theorem ch13 : allR rowK (16 * 13) 16 = true := by quickRfl
theorem ch14 : allR rowK (16 * 14) 16 = true := by quickRfl
theorem ch15 : allR rowK (16 * 15) 16 = true := by quickRfl

theorem rows (a : ℕ) (ha : a < 256) : rowK a = true := by
  have hc : ∀ j < 16, allR rowK (16 * j) 16 = true := by
    intro j hj
    interval_cases j
    exacts [ch0, ch1, ch2, ch3, ch4, ch5, ch6, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14, ch15]
  have h := allR_sound _ _ _ (hc (a / 16) (by omega)) (a % 16) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

public theorem cSideB5_all (g : SL2 × SL2) : cSideB5 g = true := by
  refine B5_sound g ?_
  have h := rows _ (cV_lt ((g.1 : SL2) : Matrix (Fin 2) (Fin 2) F4))
  have hd : Nat.beq (detK ⟪g.1⟫) 1 = true := by rw [det_one]; rfl
  rw [rowK, hd] at h
  exact (allL_iff _ _).1 h _ (mem_filtL.2 ⟨cV_lt _, by rw [det_one]; rfl⟩)

end CertificateChecks.KernelCSide
