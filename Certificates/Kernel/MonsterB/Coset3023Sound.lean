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
      rw [hb j, ite_eq_right (by omega)]
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
    rw [hb n, ite_eq_right (lt_irrefl n)]
    simp
  rw [e1, e2, e3, Model.thetaRec, hbn, ite_eq_left rfl,
    thetaRec_congr n _ a' fun j hj => by rw [hb j, ite_eq_left hj],
    combN_congr _ n _ a' fun j hj => by rw [hb j, ite_eq_left hj]]

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

theorem c3DecW_eq (n : ℕ) : decW n = Rep4371.Native.CosetEnum.dec n := by
  obtain ⟨d1, d2, d3⟩ := dec_parts n
  exact Prod.ext d1 (Prod.ext d2 d3)

theorem c3InvW_eq (x : Model.Pauli) : c3InvW x = Rep4371.Native.CosetEnum.inv x := by
  unfold c3InvW Rep4371.Native.CosetEnum.inv
  rw [pairT_eq, tb_toNat, Rep4371.native_pairN]

theorem c3GenPW_eq (k : ℕ) : c3GenPW k = Rep4371.Native.CosetEnum.gen k := by
  unfold c3GenPW Rep4371.Native.CosetEnum.gen
  by_cases h : k < 12
  · have hb : Nat.blt k 12 = true := by rwa [Nat.blt_eq]
    rw [hb, ite_eq_left h, pw2_eq' k]
  · have hb : Nat.blt k 12 = false := Bool.eq_false_iff.2 fun e => h (by rwa [Nat.blt_eq] at e)
    rw [hb, ite_eq_right h, pw2_eq' (k.sub 12)]
    rfl

theorem c3EncW_eq (x : Model.Pauli) : c3EncW x = Rep4371.Native.CosetEnum.enc x := by
  obtain ⟨s, a, d⟩ := x
  unfold c3EncW Rep4371.Native.CosetEnum.enc
  rw [land_4095, land_4095]
  cases s
  · simp
  · simp
    omega

theorem c3ImgW_eq {I : ℕ} {G : Array Model.Pauli} (hs : G.size = 24) (hI : I >>> 600 = 0)
    (h : ∀ k < 24, c3ImgW I k = G[k]!) (k : ℕ) : c3ImgW I k = G[k]! := by
  rcases Nat.lt_or_ge k 24 with hk | hk
  · exact h k hk
  · have h0 : Nat.shiftRight I (Nat.mul 25 k) = 0 := by
      change I >>> (25 * k) = 0
      rw [show 25 * k = 600 + (25 * k - 600) by omega, Nat.shiftRight_add, hI, Nat.zero_shiftRight]
    rw [getElem!_neg G k (by omega)]
    unfold c3ImgW
    rw [h0]
    rfl

theorem c3ActK_eq {I : ℕ} {G : Array Model.Pauli} (h : ∀ k, c3ImgW I k = G[k]!) :
    c3ActK I = Rep4371.Native.CosetEnum.act G := by
  funext k n
  unfold c3ActK Rep4371.Native.CosetEnum.act
  rw [h k, mulW_eq, mulW_eq, c3DecW_eq, c3GenPW_eq, c3InvW_eq, c3EncW_eq, Rep4371.native_Pauli_mul]

theorem c3GensImg_eq (h : thOK = true) {P : ℕ} {p : Array ℕ} (hP : ∀ i < 24, pe P i = p[i]!)
    (e : ℕ) : Rep4371.Native.CosetEnum.gensImg e p =
      ((List.range 24).map fun k => alphaW e (Model.pN e) P (betaTabT P) (c3GenPW k)).toArray := by
  simp only [Rep4371.Native.CosetEnum.gensImg, alphaW_eq h hP, c3GenPW_eq, Rep4371.native_conjPermN,
    Rep4371.native_conjYN]

theorem c3ThStep_eq (hpb : ∀ n < 12, fget c3PB n 12 = packBetaT n) (a : ℕ) :
    c3ThStep a = thStep a := by
  unfold c3ThStep thStep
  dsimp only
  generalize thN a = n
  cases h : Nat.blt n 12
  · rfl
  · rw [hpb n (by rwa [Nat.blt_eq] at h)]

theorem c3ThOK_eq (hpb : ∀ n < 12, fget c3PB n 12 = packBetaT n) : c3ThOK = thOK := by
  unfold c3ThOK thOK
  simp only [c3ThStep_eq hpb]

theorem c3ProdW_s (TT : ℕ → ℕ) (w : Model.Pauli) (a d : ℕ) :
    prodW TT w true a d = prodW TT w false a d := by
  unfold prodW mulW
  simp

theorem c3HW_eq (TT : ℕ → ℕ) (w : Model.Pauli) (a d : ℕ) : hW TT w a d = c3HW TT w a d := by
  unfold hW c3HW
  rw [c3ProdW_s]
  change _ + _ = 2 * _
  omega

theorem c3PartK_eq (TT : ℕ → ℕ) (w : Model.Pauli) (J : ℕ → ℕ) (k v : ℕ) :
    partOK TT w J k v = c3PartK TT w J k v := by
  unfold partOK c3PartK blockSum c3BlockSum
  simp only [c3HW_eq]

theorem c3XorSum_congr {f g : ℕ → Bool} : ∀ {n}, (∀ i < n, f i = g i) →
    Model.xorSum f n = Model.xorSum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Model.xorSum]
    rw [c3XorSum_congr fun i hi => h i (by omega), h n (by omega)]

theorem c3XorSum_succ (f : ℕ → Bool) : ∀ k,
    Model.xorSum f (k + 1) = (f 0 ^^ Model.xorSum (fun i => f (i + 1)) k)
  | 0 => by simp [Model.xorSum]
  | k + 1 => by rw [Model.xorSum, c3XorSum_succ f k, Model.xorSum, Bool.xor_assoc]

theorem c3XorSum_xor (f g : ℕ → Bool) : ∀ n,
    Model.xorSum (fun i => f i ^^ g i) n = (Model.xorSum f n ^^ Model.xorSum g n)
  | 0 => rfl
  | n + 1 => by
    simp only [Model.xorSum]
    rw [c3XorSum_xor f g n]
    have h4 : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
    exact h4 _ _ _ _

theorem c3XorSum_false : ∀ n, Model.xorSum (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by rw [Model.xorSum, c3XorSum_false n, Bool.xor_false]

theorem c3ParN_bits : ∀ k x, Model.parN k x = Model.xorSum x.testBit k
  | 0, _ => rfl
  | k + 1, x => by
    have ih := c3ParN_bits k (x / 2)
    have hf : (fun i => x.testBit (i + 1)) = (x / 2).testBit := funext fun i => Nat.testBit_succ x i
    unfold Model.parN at ih ⊢
    rw [c3XorSum_succ, hf, ← ih, Model.popcN, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (Model.popcN k (x / 2)) with h' | h' <;>
      simp [Nat.add_mod, h, h']

theorem c3TestBit_xor (x y j : ℕ) : (Nat.xor x y).testBit j = (x.testBit j ^^ y.testBit j) :=
  Nat.testBit_xor x y j

theorem c3TbPairT (x y : ℕ) :
    tb (pairT x y) = Model.xorSum (fun j => x.testBit j && y.testBit j) 12 := by
  rw [pairT_eq, tb_toNat, Model.pairN, c3ParN_bits]
  exact c3XorSum_congr fun j _ => Nat.testBit_and x y j

theorem c3Q_xorL (x y z : ℕ) : tb (pairT (Nat.xor x y) z) = (tb (pairT x z) ^^ tb (pairT y z)) := by
  rw [c3TbPairT, c3TbPairT, c3TbPairT, ← c3XorSum_xor]
  exact c3XorSum_congr fun j _ => by rw [c3TestBit_xor, Bool.and_xor_distrib_right]

theorem c3Q_xorR (x y z : ℕ) : tb (pairT x (Nat.xor y z)) = (tb (pairT x y) ^^ tb (pairT x z)) := by
  rw [c3TbPairT, c3TbPairT, c3TbPairT, ← c3XorSum_xor]
  exact c3XorSum_congr fun j _ => by rw [c3TestBit_xor, Bool.and_xor_distrib_left]

theorem c3Q_zeroL (z : ℕ) : tb (pairT 0 z) = false := by
  rw [c3TbPairT]
  exact (c3XorSum_congr fun j _ => by rw [Nat.zero_testBit, Bool.false_and]).trans
    (c3XorSum_false 12)

theorem c3Q_zeroR (x : ℕ) : tb (pairT x 0) = false := by
  rw [c3TbPairT]
  exact (c3XorSum_congr fun j _ => by rw [Nat.zero_testBit, Bool.and_false]).trans
    (c3XorSum_false 12)

theorem c3Q_lowL {x x' : ℕ} (h : ∀ j < 12, x.testBit j = x'.testBit j) (z : ℕ) :
    tb (pairT x z) = tb (pairT x' z) := by
  rw [c3TbPairT, c3TbPairT]
  exact c3XorSum_congr fun j hj => by rw [h j hj]

theorem c3Q_lowR {z z' : ℕ} (h : ∀ j < 12, z.testBit j = z'.testBit j) (x : ℕ) :
    tb (pairT x z) = tb (pairT x z') := by
  rw [c3TbPairT, c3TbPairT]
  exact c3XorSum_congr fun j hj => by rw [h j hj]

theorem c3Land_zero {x : ℕ} (h : ∀ j < 12, x.testBit j = false) : Nat.beq (Nat.land x 4095) 0 = true := by
  rw [land_4095, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hj : j < 12
  · rw [decide_eq_true hj, Bool.true_and, h j hj]
  · rw [decide_eq_false hj, Bool.false_and]

theorem c3HS_eq {TT : ℕ → ℕ} {w : Model.Pauli} {a d : ℕ} (h : kA TT w a = kD TT d) :
    c3HW TT w a d = c3HS (c3SgnA w (tabE TT a)) (tabE TT (Nat.add 4096 d)) a := by
  unfold kA kD at h
  unfold c3HW c3HS prodW
  generalize tabE TT a = t at h ⊢
  generalize tabE TT (Nat.add 4096 d) = u at h ⊢
  obtain ⟨w1, wa, wd⟩ := w
  obtain ⟨t1, ta, td⟩ := t
  obtain ⟨u1, ua, ud⟩ := u
  dsimp only at h
  rw [land_4095, land_4095, land_4095, land_4095] at h
  change (Nat.xor (Nat.xor a wa) ta) % 4096 + 4096 * (Nat.xor wd td % 4096) =
    ua % 4096 + 4096 * (Nat.xor d ud % 4096) at h
  have hA : Nat.xor (Nat.xor a wa) ta % 2 ^ 12 = ua % 2 ^ 12 := by
    change _ % 4096 = _ % 4096
    omega
  have hD : Nat.xor wd td % 2 ^ 12 = Nat.xor d ud % 2 ^ 12 := by
    change _ % 4096 = _ % 4096
    omega
  have bit : ∀ {x y : ℕ}, x % 2 ^ 12 = y % 2 ^ 12 → ∀ j < 12, x.testBit j = y.testBit j :=
    fun {x y} e j hj => by
      have := congrArg (Nat.testBit · j) e
      simpa only [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and] using this
  have bA : ∀ j < 12, ua.testBit j = (Nat.xor (Nat.xor a wa) ta).testBit j :=
    fun j hj => (bit hA j hj).symm
  have bD : ∀ j < 12, d.testBit j = (Nat.xor (Nat.xor wd td) ud).testBit j := fun j hj => by
    have e := bit hD j hj
    rw [c3TestBit_xor, c3TestBit_xor] at e
    rw [c3TestBit_xor, c3TestBit_xor, e]
    cases d.testBit j <;> cases ud.testBit j <;> rfl
  refine congrArg (fun b : Bool => Nat.mul 2 b.toNat) ?_
  unfold oneW mulW c3SgnA
  dsimp only
  rw [c3Land_zero fun j hj => ?_, c3Land_zero fun j hj => ?_]
  · have e : ∀ b, andB b (andB true true) = b := by decide
    rw [e]
    refine congrArg notB ?_
    simp only [c3Q_lowL bA, c3Q_lowR bD, c3Q_xorL, c3Q_xorR, c3Q_zeroL, c3Q_zeroR]
    generalize tb (pairT a td) = q1
    generalize tb (pairT wa td) = q2
    generalize tb (pairT ta td) = q3
    generalize tb (pairT a wd) = q4
    generalize tb (pairT wa wd) = q5
    generalize tb (pairT ta wd) = q6
    generalize tb (pairT a ud) = q7
    generalize tb (pairT wa ud) = q8
    generalize tb (pairT ta ud) = q9
    revert w1 t1 u1 q1 q2 q3 q4 q5 q6 q7 q8 q9
    decide
  all_goals
    simp only [c3TestBit_xor, Nat.zero_testBit, bA j hj, bD j hj]
    generalize a.testBit j = p1
    generalize wa.testBit j = p2
    generalize ta.testBit j = p3
    generalize wd.testBit j = p4
    generalize td.testBit j = p5
    generalize ud.testBit j = p6
    revert p1 p2 p3 p4 p5 p6
    decide

theorem c3SumN_congr {f g : ℕ → ℕ} : ∀ {n}, (∀ i < n, f i = g i) → sumN n f = sumN n g
  | 0, _ => rfl
  | n + 1, h => by
    change f n + sumN n f = g n + sumN n g
    rw [c3SumN_congr fun i hi => h i (by omega), h n (by omega)]

theorem c3BlockS_eq {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ} {a : ℕ}
    (hb : blockOK TT w J a = true) : c3BlockSum TT w J a = c3BlockS TT w J a := by
  unfold blockOK at hb
  dsimp only at hb
  rw [andB_iff, andB_iff, andB_iff, allN_iff'] at hb
  obtain ⟨-, he, -, -⟩ := hb
  exact c3SumN_congr fun j hj => c3HS_eq (Nat.eq_of_beq_eq_true (he j hj)).symm

theorem c3Blocks_all {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ}
    (h0 : blocksOK TT w J 0 2048 = true) (h1 : blocksOK TT w J 2048 2048 = true) :
    ∀ a < 4096, blockOK TT w J a = true := by
  intro a ha
  rcases Nat.lt_or_ge a 2048 with h | h
  · have := (allN_iff' _ _).1 h0 a h
    change blockOK TT w J (0 + a) = true at this
    rwa [Nat.zero_add] at this
  · have := (allN_iff' _ _).1 h1 (a - 2048) (by omega)
    change blockOK TT w J (2048 + (a - 2048)) = true at this
    rwa [show 2048 + (a - 2048) = a by omega] at this

theorem mono_of_succ {K : ℕ → ℕ} {N : ℕ} (h : ∀ j, j + 1 < N → K j ≤ K (j + 1)) :
    ∀ i j, i ≤ j → j < N → K i ≤ K j := by
  intro i j hij hj
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hij) with h' | h'
    · exact le_trans (ih (by omega) (by omega)) (h j hj)
    · rw [h']

theorem c3BlockOK_of {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ} (hs : sortOK TT J = true) {a : ℕ}
    (hb : c3BlockF TT w J a = true) : blockOK TT w J a = true := by
  rw [sortOK, andB_iff, allN_iff', allN_iff'] at hs
  obtain ⟨-, hm⟩ := hs
  have hmono := mono_of_succ (K := fun j => kD TT (jpi J j)) (N := 4096) fun j hj => by
    have := hm j (by omega)
    rwa [Nat.ble_eq] at this
  unfold c3BlockF at hb
  unfold blockOK
  dsimp only at hb ⊢
  rw [andB_iff, andB_iff] at hb
  obtain ⟨hle, hfl, hrest⟩ := hb
  rw [andB_iff, andB_iff, allN_iff']
  refine ⟨hle, fun j hj => ?_, hrest⟩
  rw [Nat.ble_eq] at hle
  generalize kA TT w a = k at hfl ⊢
  generalize jlo J a = lo at hle hfl ⊢
  generalize jn J a = n at hle hfl hj ⊢
  change lo + n ≤ 4096 at hle
  have hn : Nat.beq n 0 = false := by
    cases h : Nat.beq n 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
  rw [hn] at hfl
  change andB _ _ = true at hfl
  rw [andB_iff, Nat.beq_eq, Nat.beq_eq] at hfl
  obtain ⟨h1, h2⟩ := hfl
  change kD TT (jpi J (lo + n - 1)) = k at h2
  have a1 := hmono lo (lo + j) (by omega) (by omega)
  have a2 := hmono (lo + j) (lo + n - 1) (by omega) (by omega)
  rw [Nat.beq_eq]
  change kD TT (jpi J (lo + j)) = k
  omega

theorem c3BlocksOK_of {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ} (hs : sortOK TT J = true)
    {lo m : ℕ} (h : c3BlocksF TT w J lo m = true) : blocksOK TT w J lo m = true := by
  unfold c3BlocksF at h
  unfold blocksOK
  rw [allN_iff'] at h ⊢
  exact fun i hi => c3BlockOK_of hs (h i hi)

theorem c3PartS_eq {TT : ℕ → ℕ} {w : Model.Pauli} {J : ℕ → ℕ} {k v : ℕ} (hk : k < 8)
    (hb : ∀ a < 4096, blockOK TT w J a = true) : c3PartK TT w J k v = c3PartS TT w J k v := by
  unfold c3PartK c3PartS
  exact congrArg (Nat.beq · v) (c3SumN_congr fun i hi =>
    c3BlockS_eq (hb _ (by change 512 * k + i < 4096; omega)))

section TabHom

open CFSG.Monster.B.Rep4371 CFSG.Monster.Visible

theorem c3Xor_two_pow {n a : ℕ} (ha : a < 2 ^ n) : a ^^^ 2 ^ n = 2 ^ n + a := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hb := testBit_split ha j
  rw [Nat.mul_one] at hb
  rw [Nat.testBit_xor, Nat.testBit_two_pow, hb]
  by_cases h : j < n
  · simp [h, show n ≠ j by omega]
  · have hlow : a.testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hlow, ite_eq_right h]
    by_cases e : n = j
    · simp [e]
    · simp [e]
      omega

theorem c3TabE_lt (TT : ℕ → ℕ) (j : ℕ) : (tabE TT j).2.1 < 2 ^ 12 ∧ (tabE TT j).2.2 < 2 ^ 12 := by
  unfold tabE
  rw [c3DecW_eq, native_dec_apply]
  exact pauliDec_lt _

theorem c3ThetaRec_lt (x : ℕ) : ∀ N, Model.thetaRec N x < 2 ^ 12
  | 0 => by simp [Model.thetaRec]
  | N + 1 => by
    simp only [Model.thetaRec]
    split_ifs
    · exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (c3ThetaRec_lt x N)
        (CFSG.Monster.B.TwoA.Census.packN_lt _ 12)) (CFSG.Monster.B.TwoA.Census.packN_lt _ 12)
    · exact c3ThetaRec_lt x N

theorem c3AlphaN_lt (i : ℕ) (y : Model.Pauli) :
    (alphaN i y).2.1 < 2 ^ 12 ∧ (alphaN i y).2.2 < 2 ^ 12 := by
  unfold alphaN Model.conjPermN Model.permCN Model.coeffN Model.permDN Model.dualN Model.thetaN
  exact ⟨CFSG.Monster.B.TwoA.Census.packN_lt _ 12, Nat.xor_lt_two_pow (c3ThetaRec_lt _ 12)
    (CFSG.Monster.B.TwoA.Census.packN_lt _ 12)⟩

theorem c3Q_mul {i : ℕ} {f : ℕ → Model.Pauli} {X Y : Model.Pauli} {a b c : ℕ}
    (hc : f c = Model.Pauli.mul (f a) (f b))
    (hX : pauliQ X = conjQ (cosetPair i) (pauliQ (f a))) (hY : Y = alphaN i (f b)) :
    pauliQ (mulW X Y) = conjQ (cosetPair i) (pauliQ (f c)) := by
  subst hY
  calc pauliQ (mulW X (alphaN i (f b)))
      = pauliQ X * pauliQ (alphaN i (f b)) :=
        (congrArg pauliQ (mulW_eq X _)).trans (pauliQ_mul X _)
    _ = conjQ (cosetPair i) (pauliQ (f a)) * conjQ (cosetPair i) (pauliQ (f b)) :=
        congrArg₂ (· * ·) hX (conjQ_cosetPair i (f b)).symm
    _ = conjQ (cosetPair i) (pauliQ (f a) * pauliQ (f b)) :=
        ((conjQ (cosetPair i)).map_mul _ _).symm
    _ = conjQ (cosetPair i) (pauliQ (f c)) :=
        congrArg (fun z => conjQ (cosetPair i) z) ((pauliQ_mul _ _).symm.trans
          (congrArg pauliQ hc.symm))

theorem c3TabL_sound {TT : ℕ → ℕ} {o i : ℕ} {f : ℕ → Model.Pauli}
    (hf : ∀ a b, f (a ^^^ b) = Model.Pauli.mul (f a) (f b)) (hf0 : f 0 = (false, 0, 0))
    (hL : c3TabL TT o = true) (hB : ∀ n < 12, tabE TT (o + 2 ^ n) = alphaN i (f (2 ^ n))) :
    ∀ A < 2 ^ 12, tabE TT (o + A) = alphaN i (f A) := by
  rw [c3TabL, andB_iff, allN_iff'] at hL
  obtain ⟨h0, hL⟩ := hL
  have hP : ∀ A < 2 ^ 12, pauliQ (tabE TT (o + A)) = conjQ (cosetPair i) (pauliQ (f A)) := by
    intro A
    induction A using Nat.strong_induction_on with
    | _ A ih =>
      intro hA
      rcases Nat.eq_zero_or_pos A with rfl | hpos
      · rw [Nat.add_zero, of_decide_eq_true h0, hf0, pauliQ_false_zero, map_one]
      · have h1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.1 hpos)
        have h2 := Nat.lt_log2_self (n := A)
        rw [pow_succ] at h2
        obtain ⟨n, hn, a, ha, rfl⟩ : ∃ n < 12, ∃ a < 2 ^ n, A = 2 ^ n + a := by
          refine ⟨A.log2, ?_, A - 2 ^ A.log2, by omega, by omega⟩
          by_contra h
          have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.1 h)
          omega
        have hs := hL n hn
        rw [pw2_eq', allN_iff'] at hs
        have he := of_decide_eq_true (hs a ha)
        have hpos' := Nat.two_pow_pos n
        change tabE TT (o + (2 ^ n + a)) = mulW (tabE TT (o + a)) (tabE TT (o + 2 ^ n)) at he
        have hc : f (2 ^ n + a) = Model.Pauli.mul (f a) (f (2 ^ n)) := by
          rw [← c3Xor_two_pow ha]
          exact hf a (2 ^ n)
        rw [he]
        exact c3Q_mul hc (ih a (by omega) (by omega)) (hB n hn)
  intro A hA
  have hT := c3TabE_lt TT (o + A)
  have hN := c3AlphaN_lt i (f A)
  exact pauliQ_inj hT.1 hT.2 hN.1 hN.2 ((hP A hA).trans (conjQ_cosetPair i (f A)))

theorem c3Tab_spec {c : ℕ} {TT : ℕ → ℕ} {e : ℕ} {pe : Bool} {P BT : ℕ}
    (hα : ∀ y, alphaW e pe P BT y = alphaN c y) (hLA : c3TabL TT 0 = true)
    (hLD : c3TabL TT 4096 = true) (ha : c3TabBA TT e pe P BT = true)
    (hd : c3TabBD TT e pe P BT = true) : TabSpec TT (tT c) (tD c) := by
  rw [c3TabBA, allN_iff'] at ha
  rw [c3TabBD, allN_iff'] at hd
  refine ⟨fun A hA => ?_, fun D hD => ?_⟩
  · have h := c3TabL_sound (o := 0) (i := c) (f := fun a => (false, a, 0))
      (fun a b => by
        simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, Model.pairN,
          Nat.and_zero, Nat.xor_zero]
        rfl)
      rfl hLA (fun n hn => by
        have hb := of_decide_eq_true (ha n hn)
        rw [pw2_eq', hα] at hb
        rw [Nat.zero_add]
        exact hb.symm) A hA
    rw [Nat.zero_add] at h
    rw [tT_get c hA, h]
  · have h := c3TabL_sound (o := 4096) (i := c) (f := fun d => (false, 0, d))
      (fun a b => by
        simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, Model.pairN,
          Nat.zero_and, Nat.xor_zero]
        rfl)
      rfl hLD (fun n hn => by
        have hb := of_decide_eq_true (hd n hn)
        rw [pw2_eq', hα] at hb
        exact hb.symm) D hD
    rw [tD_get c hD]
    exact h.symm

end TabHom

end CertificateChecks.Coset3023

end
