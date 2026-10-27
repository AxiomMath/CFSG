module

public import Certificates.Kernel.MonsterB.Coset3023Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.Coset3023

open CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.KLie.CT CFSG.Monster.B CFSG.KC.SortTree
  CFSG.Monster.B.TwoA.Census

theorem allN_iff' (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [show ∀ a b : Bool, andB a b = (a && b) from fun a b => by cases a <;> rfl,
      Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem pw2_eq' (w : ℕ) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem land_4095 (x : ℕ) : Nat.land x 4095 = x % 2 ^ 12 :=
  Nat.and_two_pow_sub_one_eq_mod x 12

theorem nbeq (a b : ℕ) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, beq_iff_eq])

theorem tb_toNat (b : Bool) : tb b.toNat = b := by cases b <;> rfl

theorem combN_congr (m : ℕ → ℕ) : ∀ n a b, (∀ j < n, a.testBit j = b.testBit j) →
    Model.combN m n a = Model.combN m n b
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    rw [Model.combN, Model.combN, combN_congr m n a b fun j hj => h j (by omega), h n (by omega)]

theorem combN_high (m : ℕ → ℕ) (n : ℕ) : ∀ k a, (∀ j, n ≤ j → j < n + k → a.testBit j = false) →
    Model.combN m (n + k) a = Model.combN m n a
  | 0, _, _ => rfl
  | k + 1, a, h => by
    rw [← Nat.add_assoc, Model.combN, combN_high m n k a fun j h1 h2 => h j h1 (by omega),
      h (n + k) (by omega) (by omega)]
    simp

theorem thetaRec_congr : ∀ n a b, (∀ j < n, a.testBit j = b.testBit j) →
    Model.thetaRec n a = Model.thetaRec n b
  | 0, _, _, _ => rfl
  | n + 1, a, b, h => by
    rw [Model.thetaRec, Model.thetaRec, thetaRec_congr n a b fun j hj => h j (by omega),
      combN_congr _ n a b fun j hj => h j (by omega), h n (by omega)]

theorem thetaRec_high (n : ℕ) : ∀ k a, (∀ j, n ≤ j → j < n + k → a.testBit j = false) →
    Model.thetaRec (n + k) a = Model.thetaRec n a
  | 0, _, _ => rfl
  | k + 1, a, h => by
    rw [← Nat.add_assoc, Model.thetaRec, thetaRec_high n k a fun j h1 h2 => h j h1 (by omega),
      h (n + k) (by omega) (by omega)]
    simp

theorem thetaN_mod (x : ℕ) : Model.thetaN x = Model.thetaN (x % 2 ^ 12) :=
  thetaRec_congr 12 _ _ fun j hj => by rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]

theorem testBit_split {n a' : ℕ} (ha : a' < 2 ^ n) (j : ℕ) :
    (2 ^ n * 1 + a').testBit j = if j < n then a'.testBit j else decide (j - n = 0) := by
  rw [Nat.testBit_two_pow_mul_add 1 ha]
  split
  · rfl
  · by_cases hj : j - n = 0
    · rw [hj]
      rfl
    · rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hj)]
      simp [hj]

theorem thetaRec_zero : ∀ n, Model.thetaRec n 0 = 0
  | 0 => rfl
  | n + 1 => by
    rw [Model.thetaRec, Nat.zero_testBit]
    exact thetaRec_zero n

theorem thetaN_split {n a' : ℕ} (hn : n < 12) (ha : a' < 2 ^ n) :
    Model.thetaN (2 ^ n * 1 + a') = Model.thetaN a' ^^^ Model.packN (Model.betaN n) 12 ^^^
      Model.dualN (Model.combN Model.bmaskN 12 a' &&& Model.bmaskN n) := by
  have hb := testBit_split ha
  have hlow : ∀ j, n ≤ j → a'.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hj))
  unfold Model.thetaN
  have e1 : Model.thetaRec 12 (2 ^ n * 1 + a') = Model.thetaRec (n + 1) (2 ^ n * 1 + a') := by
    have := thetaRec_high (n + 1) (11 - n) (2 ^ n * 1 + a') fun j h1 h2 => by
      rw [hb j, if_neg (by omega)]
      simp
      omega
    rwa [show n + 1 + (11 - n) = 12 by omega] at this
  have e2 : Model.thetaRec 12 a' = Model.thetaRec n a' := by
    have := thetaRec_high n (12 - n) a' fun j h1 _ => hlow j h1
    rwa [show n + (12 - n) = 12 by omega] at this
  have e3 : Model.combN Model.bmaskN 12 a' = Model.combN Model.bmaskN n a' := by
    have := combN_high Model.bmaskN n (12 - n) a' fun j h1 _ => hlow j h1
    rwa [show n + (12 - n) = 12 by omega] at this
  have hbn : (2 ^ n * 1 + a').testBit n = true := by
    rw [hb n, if_neg (lt_irrefl n)]
    simp
  rw [e1, e2, e3, Model.thetaRec, hbn, if_pos rfl,
    thetaRec_congr n _ a' fun j hj => by rw [hb j, if_pos hj],
    combN_congr _ n _ a' fun j hj => by rw [hb j, if_pos hj]]

theorem thetaL_lt (h : thOK = true) : ∀ a < 2 ^ 12, thetaL a = Model.thetaN a := by
  rw [thOK, andB_iff, andB_iff, allN_iff'] at h
  obtain ⟨h0, -, hs⟩ := h
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [Nat.beq_eq] at h0
      rw [h0]
      exact (thetaRec_zero 12).symm
    · have hst := hs (a - 1) (by omega)
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hpos] at hst
      unfold thStep at hst
      dsimp only at hst
      rw [andB_iff, andB_iff, andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq,
        pw2_eq'] at hst
      obtain ⟨hn, hle, hlt, he⟩ := hst
      generalize thN a = n at hn hle hlt he
      change a - 2 ^ n < 2 ^ n at hlt
      change thetaL a = thetaL (a - 2 ^ n) ^^^ packBetaT n ^^^
        dualT (wordT (a - 2 ^ n) &&& bmT n) at he
      have ha' : 2 ^ n * 1 + (a - 2 ^ n) = a := by omega
      rw [he, ih _ (by omega) (by omega), packBetaT_eq n hn, dualT_eq, wordT_eq, bmT_eq n hn,
        Model.wordN, ← thetaN_split hn hlt, ha']

theorem thetaL_eq (h : thOK = true) (x : ℕ) : thetaL x = Model.thetaN x := by
  have e : thetaL x = thetaL (x % 2 ^ 12) := by
    have e' : Nat.land x 4095 = Nat.land (x % 2 ^ 12) 4095 := by
      rw [land_4095, land_4095, Nat.mod_mod]
    unfold thetaL
    rw [e']
  rw [e, thetaL_lt h _ (Nat.mod_lt _ (by norm_num)), ← thetaN_mod]

theorem mulW_eq (x y : Model.Pauli) : mulW x y = Model.Pauli.mul x y := by
  obtain ⟨s, a, d⟩ := x
  obtain ⟨t, b, e⟩ := y
  unfold mulW Model.Pauli.mul
  rw [pairT_eq, tb_toNat]
  rfl

theorem conjTW_eq (h : thOK = true) (e b : ℕ) : conjTW e b = Model.conjTN e b := by
  unfold conjTW Model.conjTN Model.thetaBit Model.acodeN
  rw [thetaL_eq h, thetaL_eq h, pairT_eq, pairT_eq, tb_toNat, selB_toNat, wordT_eq, wordT_eq,
    dualT_eq]
  rfl

theorem conjDW_eq (h : thOK = true) (e d : ℕ) : conjDW e (Model.pN e) d = Model.conjDN e d := by
  unfold conjDW Model.conjDN
  rw [pairT_eq, pairT_eq, thetaL_eq h]
  cases Model.pairN 63 d <;> cases Model.pairN e d <;> cases Model.pN e <;> simp [selB, tb] <;> rfl

theorem conjYW_eq (h : thOK = true) (e : ℕ) (y : Model.Pauli) :
    conjYW e (Model.pN e) y = Model.conjYN e y := by
  unfold conjYW Model.conjYN
  rw [mulW_eq, mulW_eq, conjTW_eq h, conjDW_eq h]

theorem conjPermW_eq (h : thOK = true) {P : ℕ} {p : Array ℕ} (hP : ∀ i < 24, pe P i = p[i]!)
    (y : Model.Pauli) : conjPermW P (betaTabT P) y = Model.conjPermN p y := by
  unfold conjPermW Model.conjPermN
  rw [kappaT_eq hP, tb_toNat, permCT_eq hP, thetaL_eq h, thetaL_eq h, permDT_eq hP]
  rfl

theorem alphaW_eq (h : thOK = true) {P : ℕ} {p : Array ℕ} (hP : ∀ i < 24, pe P i = p[i]!)
    (e : ℕ) (y : Model.Pauli) :
    alphaW e (Model.pN e) P (betaTabT P) y = Model.conjPermN p (Model.conjYN e y) := by
  unfold alphaW
  rw [conjYW_eq h, conjPermW_eq h hP]

@[expose] def TabSpec (TT : ℕ → ℕ) (tA tB : Array Model.Pauli) : Prop :=
  (∀ A < 2 ^ 12, tA[A]! = tabE TT A) ∧ ∀ D < 2 ^ 12, tB[D]! = tabE TT (Nat.add 4096 D)

theorem xor_mod_eq {x y : ℕ} (h : (x ^^^ y) % 2 ^ 12 = 0) : x % 2 ^ 12 = y % 2 ^ 12 := by
  rw [Nat.xor_mod_two_pow] at h
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun z => z.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  cases hx : (x % 2 ^ 12).testBit i <;> cases hy : (y % 2 ^ 12).testBit i <;> simp_all

theorem key_eq {a d : ℕ} {w t u : Model.Pauli}
    (ha : (a ^^^ (w.2.1 ^^^ (0 ^^^ (t.2.1 ^^^ u.2.1)))) % 2 ^ 12 = 0)
    (hd : (d ^^^ (w.2.2 ^^^ (0 ^^^ (t.2.2 ^^^ u.2.2)))) % 2 ^ 12 = 0) :
    Nat.add (Nat.land (Nat.xor (Nat.xor a w.2.1) t.2.1) 4095)
        (Nat.mul 4096 (Nat.land (Nat.xor w.2.2 t.2.2) 4095)) =
      Nat.add (Nat.land u.2.1 4095) (Nat.mul 4096 (Nat.land (Nat.xor d u.2.2) 4095)) := by
  rw [land_4095, land_4095, land_4095, land_4095]
  have h1 : ((a ^^^ w.2.1 ^^^ t.2.1) ^^^ u.2.1) % 2 ^ 12 = 0 := by
    rw [← ha]
    congr 1
    simp only [Nat.zero_xor, Nat.xor_assoc]
  have h2 : ((w.2.2 ^^^ t.2.2) ^^^ (d ^^^ u.2.2)) % 2 ^ 12 = 0 := by
    rw [← hd]
    congr 1
    simp only [Nat.zero_xor]
    ac_rfl
  change (a ^^^ w.2.1 ^^^ t.2.1) % 2 ^ 12 + 4096 * ((w.2.2 ^^^ t.2.2) % 2 ^ 12) =
    u.2.1 % 2 ^ 12 + 4096 * ((d ^^^ u.2.2) % 2 ^ 12)
  rw [xor_mod_eq h1, xor_mod_eq h2]

theorem dec_parts (n : ℕ) : tb (Nat.land (Nat.shiftRight n 24) 1) = n.testBit 24 ∧
    Nat.land n 4095 = n % 2 ^ 12 ∧ Nat.land (Nat.shiftRight n 12) 4095 = n / 2 ^ 12 % 2 ^ 12 := by
  refine ⟨?_, land_4095 n, ?_⟩
  · change tb ((n >>> 24) &&& 1) = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ 24) with h | h <;> rw [h] <;> rfl
  · rw [land_4095]
    change (n >>> 12) % 2 ^ 12 = _
    rw [Nat.shiftRight_eq_div_pow]

theorem sqTest_eq_sqW {TT : ℕ → ℕ} {tA tB : Array Model.Pauli} (hT : TabSpec TT tA tB)
    (w : Model.Pauli) (n : ℕ) :
    Rep4371.Native.CosetEnum.sqTest tA tB w n = sqW TT w n := by
  obtain ⟨d1, d2, d3⟩ := dec_parts n
  have hA := hT.1 (n % 2 ^ 12) (Nat.mod_lt _ (by norm_num))
  have hB := hT.2 (n / 2 ^ 12 % 2 ^ 12) (Nat.mod_lt _ (by norm_num))
  rw [sqTest_eq_isOne]
  unfold sqW
  rw [d1, d2, d3]
  unfold Rep4371.Native.CosetEnum.sqProd Rep4371.Native.CosetEnum.dec
  dsimp only
  rw [hA, hB, Rep4371.native_Pauli_mul]
  unfold kA kD prodW
  simp only [mulW_eq]
  generalize tabE TT (n % 2 ^ 12) = t
  generalize tabE TT (Nat.add 4096 (n / 2 ^ 12 % 2 ^ 12)) = u
  generalize n.testBit 24 = s
  generalize n % 2 ^ 12 = a
  generalize n / 2 ^ 12 % 2 ^ 12 = d
  generalize hP : Model.Pauli.mul (s, a, d)
    (Model.Pauli.mul w (Model.Pauli.mul (s, 0, 0) (Model.Pauli.mul t u))) = P
  have hPa : P.2.1 = a ^^^ (w.2.1 ^^^ (0 ^^^ (t.2.1 ^^^ u.2.1))) := by rw [← hP]; rfl
  have hPd : P.2.2 = d ^^^ (w.2.2 ^^^ (0 ^^^ (t.2.2 ^^^ u.2.2))) := by rw [← hP]; rfl
  have hone : oneW P = Rep4371.Native.CosetEnum.isOne P := by
    unfold oneW Rep4371.Native.CosetEnum.isOne
    rw [land_4095, land_4095, nbeq, nbeq]
    cases P.1 <;> cases (P.2.1 % 2 ^ 12 == 0) <;> cases (P.2.2 % 2 ^ 12 == 0) <;> rfl
  rw [hone]
  cases hI : Rep4371.Native.CosetEnum.isOne P
  · cases Nat.beq _ _ <;> rfl
  · have h := hI
    simp only [Rep4371.Native.CosetEnum.isOne, Bool.and_eq_true, beq_iff_eq] at h
    rw [key_eq (hPa ▸ h.1.2) (hPd ▸ h.2), Nat.beq_refl]
    rfl

end CertificateChecks.Coset3023

end
