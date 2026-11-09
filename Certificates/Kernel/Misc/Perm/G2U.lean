module

public import Certificates.Kernel.Misc.Perm.G2UK
public import CFSG.Certificates.Kernel.Misc.PermG2USound
public import CFSG.Quasithin.Background.G2UGroupsInputs

public section

namespace CertificateChecks.KernelMisc.G2U

open Matrix CFSG.KC.Misc.Clos CFSG.KC.Misc.G2U CFSG.Quasithin.G2U

private theorem fld14_lt (y o : Nat) : fldN y o 14 < 2 ^ 14 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private noncomputable def bitG (x y i j n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun k acc => acc ^^ (x.testBit (14 * i + k) && (fldN y (14 * k) 14).testBit j)) n

private theorem blt_land (x p : Nat) :
    Nat.blt 0 (Nat.land x (Nat.shiftLeft 1 p)) = x.testBit p := by
  have h : Nat.land x (Nat.shiftLeft 1 p) = (x.testBit p).toNat * 2 ^ p := by
    change x &&& 1 <<< p = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow]
  rw [h]
  cases x.testBit p
  · rw [Bool.toNat_false, Nat.zero_mul]
    rfl
  · simp [Nat.blt_eq]

private theorem row2N_spec (x y i j n : Nat) :
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.xor acc (fldN y (Nat.mul 14 k) 14))
        (Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul 14 i) k)))))
      n).testBit j = bitG x y i j n ∧
    (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.xor acc (fldN y (Nat.mul 14 k) 14))
        (Nat.blt (nat_lit 0) (Nat.land x (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul 14 i) k)))))
      n) < 2 ^ 14 := by
  induction n with
  | zero => exact ⟨by simp [bitG], Nat.two_pow_pos 14⟩
  | succ n ih =>
    simp only [bitG] at ih ⊢
    rw [blt_land]
    cases hb : x.testBit (Nat.add (Nat.mul 14 i) n)
    · refine ⟨?_, ih.2⟩
      simp only [ih.1]
      simp
    · refine ⟨?_, Nat.xor_lt_two_pow ih.2 (fld14_lt _ _)⟩
      change ((_ : Nat) ^^^ _).testBit j = _
      rw [Nat.testBit_xor, ih.1]
      simp

private theorem m2_spec (x y b : Nat) :
    (m2 x y).testBit b = (decide (b < 196) && bitG x y (b / 14) (b % 14) 14) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor acc (Nat.shiftLeft (row2 x y i) (Nat.mul 14 i))) n).testBit b =
      (decide (b < 14 * n) && bitG x y (b / 14) (b % 14) 14) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change (_ ||| _ <<< (14 * n)).testBit b = _
      rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      have hr := row2N_spec x y n (b - 14 * n) 14
      change (row2 x y n).testBit _ = _ ∧ row2 x y n < _ at hr
      by_cases h1 : b < 14 * n
      · have : ¬ b ≥ 14 * n := by omega
        simp [h1, this, show b < 14 * (n + 1) by omega]
      · by_cases h2 : b < 14 * (n + 1)
        · have hq : b / 14 = n := by omega
          have hm : b % 14 = b - 14 * n := by omega
          simp [h1, h2, show b ≥ 14 * n by omega, hq, hm, hr.1]
        · have hz : (row2 x y n).testBit (b - 14 * n) = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr.2 (Nat.pow_le_pow_right (by norm_num)
              (by omega)))
          simp [h1, h2, hz]
  exact key 14

private theorem mul_sel (r : Nat) (hr : r < 2 ^ 14) : ∀ s, (∀ c, s.testBit c = true → c % 14 = 0) →
    ∀ b, (s * r).testBit b = (s.testBit (14 * (b / 14)) && r.testBit (b % 14)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs b
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · simp
    have hm : s % 2 ^ 14 = (s.testBit 0).toNat := by
      apply Nat.eq_of_testBit_eq
      intro c
      rw [Nat.testBit_mod_two_pow]
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · cases s.testBit 0 <;> simp
      · have h1 : (s.testBit 0).toNat.testBit c = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Bool.toNat_le _)
            (Nat.one_lt_two_pow (by omega)))
        rw [h1]
        by_cases hc14 : c < 14
        · have : s.testBit c = false := by
            by_contra hne
            have := hs c (by simpa using hne)
            omega
          simp [this]
        · simp [hc14]
    have hd : s * r = 2 ^ 14 * (s / 2 ^ 14 * r) + (s.testBit 0).toNat * r := by
      rw [← hm, ← Nat.mul_assoc, ← Nat.add_mul, Nat.div_add_mod]
    have hlt : (s.testBit 0).toNat * r < 2 ^ 14 := by
      cases s.testBit 0
      · simp
      · simpa using hr
    rw [hd, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hb : b < 14
    · have hq : b / 14 = 0 := by omega
      have hmb : b % 14 = b := by omega
      simp only [hb, ↓reduceIte]
      rw [hq, hmb]
      cases s.testBit 0 <;> simp
    · simp only [hb, ↓reduceIte]
      have hs' : ∀ c, (s / 2 ^ 14).testBit c = true → c % 14 = 0 := by
        intro c hc
        rw [Nat.testBit_div_two_pow] at hc
        have := hs _ hc
        omega
      rw [ih _ (Nat.div_lt_self hpos (by norm_num)) hs', Nat.testBit_div_two_pow]
      have e1 : 14 * ((b - 14) / 14) + 14 = 14 * (b / 14) := by omega
      have e2 : (b - 14) % 14 = b % 14 := by omega
      rw [e1, e2]

private theorem onesC_bit (c : Nat) :
    onesC.testBit c = (decide (c < 196) && decide (c % 14 = 0)) := by
  by_cases hc : c < 196
  · have h : ∀ c < 196, onesC.testBit c = decide (c % 14 = 0) := by
      decide +kernel
    simp [hc, h c hc]
  · have : onesC < 2 ^ c := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by norm_num)
      (by omega : 196 ≤ c))
    simp [hc, Nat.testBit_lt_two_pow this]

private theorem m2W_spec (x y b : Nat) :
    (m2W x y).testBit b = (decide (b < 196) && bitG x y (b / 14) (b % 14) 14) := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.xor acc
        (Nat.mul (Nat.land (Nat.shiftRight x k) onesC) (fldN y (Nat.mul 14 k) 14))) n).testBit b =
      (decide (b < 196) && bitG x y (b / 14) (b % 14) n) := by
    intro n
    induction n with
    | zero => simp [bitG]
    | succ n ih =>
      change (_ ^^^ ((x >>> n &&& onesC) * fldN y (14 * n) 14)).testBit b = _
      have hsel : ∀ c, (x >>> n &&& onesC).testBit c = true → c % 14 = 0 := by
        intro c hc
        rw [Nat.testBit_and, onesC_bit] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.2.2
      rw [Nat.testBit_xor, ih, mul_sel _ (fld14_lt _ _) _ hsel, Nat.testBit_and,
        Nat.testBit_shiftRight, onesC_bit]
      simp only [bitG]
      have e : (decide (14 * (b / 14) < 196)) = decide (b < 196) := by
        congr 1
        apply propext
        omega
      rw [e, show n + 14 * (b / 14) = 14 * (b / 14) + n by omega]
      cases decide (b < 196) <;> simp
  exact key 14

theorem m2W_eq : m2W = m2 := by
  funext x y
  exact Nat.eq_of_testBit_eq fun b => by rw [m2W_spec, m2_spec]

private theorem lk16_mul : ∀ a < 16, ∀ b < 16, lk16 mul9T a b = mul9K a b := by
  decide +kernel

private theorem lk16_add : ∀ a < 16, ∀ b < 16, lk16 add9T a b = add9K a b := by
  decide +kernel

private theorem mod3_lt (A B : Nat) : Nat.add (Nat.mod A 3) (Nat.mul 3 (Nat.mod B 3)) < 16 := by
  have h1 := Nat.mod_lt A (by decide : 3 > 0)
  have h2 := Nat.mod_lt B (by decide : 3 > 0)
  change A % 3 + 3 * (B % 3) < 16
  omega

private theorem mul9K_lt (a b : Nat) : mul9K a b < 16 :=
  mod3_lt _ _

private theorem add9K_lt (a b : Nat) : add9K a b < 16 :=
  mod3_lt _ _

private theorem e9_lt (x k : Nat) : e9 x k < 16 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem ent9W_eq : ent9W = ent9 := by
  funext x y i j
  unfold ent9W ent9
  rw [lk16_mul _ (e9_lt _ _) _ (e9_lt _ _), lk16_mul _ (e9_lt _ _) _ (e9_lt _ _),
    lk16_mul _ (e9_lt _ _) _ (e9_lt _ _), lk16_add _ (mul9K_lt _ _) _ (mul9K_lt _ _),
    lk16_add _ (add9K_lt _ _) _ (mul9K_lt _ _)]

theorem mPW_eq : mPW = mP := by
  funext x y
  unfold mPW m9W
  rw [m2W_eq, ent9W_eq]
  rfl

private theorem e9_row (x i t : Nat) (ht : t < 3) :
    e9 x (3 * i + t) = e9 (fldN x (12 * i) 12) t := by
  change x >>> (4 * (3 * i + t)) &&& (1 <<< 4 - 1) =
    (x >>> (12 * i) &&& (1 <<< 12 - 1)) >>> (4 * t) &&& (1 <<< 4 - 1)
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow_sub_one]
  by_cases hb : b < 4
  · have e : 4 * (3 * i + t) + b = 12 * i + (4 * t + b) := by omega
    have h12 : 4 * t + b < 12 := by omega
    simp [hb, e, h12]
  · simp [hb]

private theorem ent9W_row (x y i j : Nat) :
    ent9W x y i j = ent9W (fldN x (Nat.mul 12 i) 12) y 0 j := by
  have h0 : e9 x (Nat.mul 3 i) = e9 (fldN x (Nat.mul 12 i) 12) 0 := e9_row x i 0 (by decide)
  have h1 : e9 x (Nat.add (Nat.mul 3 i) 1) = e9 (fldN x (Nat.mul 12 i) 12) 1 :=
    e9_row x i 1 (by decide)
  have h2 : e9 x (Nat.add (Nat.mul 3 i) 2) = e9 (fldN x (Nat.mul 12 i) 12) 2 :=
    e9_row x i 2 (by decide)
  unfold ent9W
  rw [h1, h2, h0]

private theorem fldN12_lt (x o : Nat) : fldN x o 12 < 4096 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem m9Tab_eq (T y : Nat) (hT : ∀ r < 4096, ∀ j < 3, e9 (row12T T r) j = ent9W r y 0 j)
    (x : Nat) : m9Tab T x = m9W x y := by
  have h : ∀ k, ent9T T x (Nat.div k 3) (Nat.mod k 3) = ent9W x y (Nat.div k 3) (Nat.mod k 3) := by
    intro k
    rw [ent9W_row]
    exact hT _ (fldN12_lt _ _) _ (Nat.mod_lt _ (by decide))
  unfold m9Tab m9W
  simp only [h]

private theorem rtab9_spec {T y : Nat} (h : tab9OK T y = true) :
    ∀ r < 4096, ∀ j < 3, e9 (row12T T r) j = ent9W r y 0 j := by
  intro r hr j hj
  have h1 := (allR_iff _ _ _).1 h r (Nat.zero_le _) (by omega)
  exact Nat.eq_of_beq_eq_true ((allR_iff _ _ _).1 h1 j (Nat.zero_le _) (by omega))

set_option maxRecDepth 400000 in
private theorem rtab9A_ok : tab9OK rtab9A gd9A = true := by
  decide +kernel

set_option maxRecDepth 400000 in
private theorem rtab9B_ok : tab9OK rtab9B gd9B = true := by
  decide +kernel
theorem m9G_eq : m9G = m9W := by
  funext x y
  unfold m9G
  cases hA : Nat.beq y gd9A
  · cases hB : Nat.beq y gd9B
    · rfl
    · rw [Nat.eq_of_beq_eq_true hB]
      exact m9Tab_eq _ _ (rtab9_spec rtab9B_ok) x
  · rw [Nat.eq_of_beq_eq_true hA]
    exact m9Tab_eq _ _ (rtab9_spec rtab9A_ok) x

theorem mPG_eq : mPG = mPW := by
  funext x y
  unfold mPG mPW
  rw [m9G_eq]

theorem rtAll : ∀ i < 12096, treeAt m2 (rows2 id2) GR 4 RE RP i = true := by
  rw [← m2W_eq]
  exact forall_of_chunks 1008 12 _ fun c hc => RTK.all c hc

theorem rsAll : ∀ i < 12096, sortAt 12096 RE RS i = true :=
  forall_of_chunks 1008 12 _ fun c hc => RSK.all c hc

theorem rcAll : ∀ i < 12096, closedAt m2 GR 4 12096 RE RC i = true := by
  rw [← m2W_eq]
  exact forall_of_chunks 1008 12 _ fun c hc => RCK.all c hc

theorem dtAll : ∀ i < 6048, treeAt mP oneD GD 2 DE DP i = true := by
  rw [← mPW_eq, ← mPG_eq]
  exact forall_of_chunks 1008 6 _ fun c hc => DTK.all c hc

theorem dsAll : ∀ i < 6048, sortAt 6048 DE DS i = true :=
  forall_of_chunks 1008 6 _ fun c hc => DSK.all c hc

theorem dcAll : ∀ i < 6048, closedAt mP GD 2 6048 DE DC i = true := by
  rw [← mPW_eq, ← mPG_eq]
  exact forall_of_chunks 1008 6 _ fun c hc => DCK.all c hc

theorem dpAll : ∀ i < 6048, pairAt (rows2 id2) (codes9 id3) DE i = true :=
  forall_of_chunks 1008 6 _ fun c hc => DPK.all c hc

theorem canon_g : canon2 g0c = true ∧ canon2 g1c = true ∧ canon2 g2c = true ∧ canon2 g3c = true ∧
    canon2 id2 = true ∧ canon3 Ac = true ∧ canon3 Bc = true ∧ canon3 id3 = true ∧
    canon2 ac = true ∧ canon2 bc = true := by
  decide +kernel

theorem gr_codes : GR 0 = rows2 g0c ∧ GR 1 = rows2 g1c ∧ GR 2 = rows2 g2c ∧ GR 3 = rows2 g3c := by
  decide +kernel

theorem gd_codes : GD 0 = codes9 Ac + 2 ^ 36 * rows2 ac ∧ GD 1 = codes9 Bc + 2 ^ 36 * rows2 bc := by
  decide +kernel

theorem one2 : encG2 1 = rows2 id2 := by
  rw [encG2, Units.val_one, ← dec2_id2, encM2_dec2 canon_g.2.2.2.2.1]

theorem one9 : encG9 1 = codes9 id3 := by
  rw [encG9, Units.val_one, ← dec3_id3, encM9_dec3 canon_g.2.2.2.2.2.2.2.1]

theorem oneGP : encGP 1 = oneD := by
  change encG9 1 + 2 ^ 36 * encG2 1 = _
  rw [one9, one2]
  rfl

abbrev gensR' : List (GL (Fin 14) (ZMod 2)) := [gen0, gen1, gen2, gen3]

theorem hGR : ∀ j < gensR'.length, GR j = encG2 (gensR'.getD j 1) := by
  intro j hj
  have hj4 : j < 4 := hj
  interval_cases j
  · rw [gr_codes.1]
    exact (encM2_dec2 canon_g.1).symm
  · rw [gr_codes.2.1]
    exact (encM2_dec2 canon_g.2.1).symm
  · rw [gr_codes.2.2.1]
    exact (encM2_dec2 canon_g.2.2.1).symm
  · rw [gr_codes.2.2.2]
    exact (encM2_dec2 canon_g.2.2.2.1).symm

abbrev gensD' : List (GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) := [(aU, AU), (bU, BU)]

private theorem gdP_of (g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) {c2 c9 : List Nat} {G : Nat}
    (h2 : (g.1 : Matrix (Fin 14) (Fin 14) (ZMod 2)) = dec2 c2)
    (h9 : (g.2 : Matrix (Fin 3) (Fin 3) F9) = dec3 c9) (k2 : canon2 c2 = true)
    (k9 : canon3 c9 = true) (hG : G = codes9 c9 + 2 ^ 36 * rows2 c2) : G = encGP g := by
  rw [hG, encGP, encG9, encG2, h2, h9, encM9_dec3 k9, encM2_dec2 k2]

theorem hGD : ∀ j < gensD'.length, GD j = encGP (gensD'.getD j 1) := by
  intro j hj
  match j, hj with
  | 0, _ =>
    exact gdP_of (aU, AU) coe_aU rfl canon_g.2.2.2.2.2.2.2.2.1 canon_g.2.2.2.2.2.1 gd_codes.1
  | 1, _ =>
    exact gdP_of (bU, BU) coe_bU rfl canon_g.2.2.2.2.2.2.2.2.2 canon_g.2.2.2.2.2.2.1 gd_codes.2
  | _ + 2, h => exact absurd h (by simp)

theorem R_eq : rootGroup = Subgroup.closure {g | g ∈ gensR'} := by
  rw [rootGroup]
  congr 1
  ext z
  simp

theorem D_eq : graphD = Subgroup.closure {g | g ∈ gensD'} := by
  rw [graphD]
  congr 1
  ext z
  simp

theorem cardR : Nat.card rootGroup = 12096 := by
  rw [R_eq]
  have ht : ∀ k < 12096, treeAt m2 (encG2 1) GR gensR'.length RE RP k = true := by
    rw [one2]
    exact rtAll
  exact ((clos_card enc2 gensR' hGR (by norm_num) ht rsAll).2.2 rcAll).1

abbrev Dg : Subgroup (GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) := Subgroup.closure {g | g ∈ gensD'}

theorem closD : (∀ k < 6048, ∃ g ∈ Dg, encGP g = DE k) ∧ 6048 ≤ Nat.card Dg ∧
    ∀ {CT : Nat → Nat}, (∀ k < 6048, closedAt mP GD gensD'.length 6048 DE CT k = true) →
      Nat.card Dg = 6048 ∧ ∀ g ∈ Dg, ∃ k < 6048, encGP g = DE k := by
  have ht : ∀ k < 6048, treeAt mP (encGP 1) GD gensD'.length DE DP k = true := by
    rw [oneGP]
    exact dtAll
  exact clos_card encP gensD' hGD (by norm_num) ht dsAll

theorem pair_spec (E : Nat → Nat) (k : Nat) (h : pairAt (rows2 id2) (codes9 id3) E k = true) :
    Nat.shiftRight (E k) 36 = rows2 id2 ↔ fldN (E k) 0 36 = codes9 id3 := by
  unfold pairAt at h
  rw [letB_eq] at h
  generalize E k = c at h ⊢
  generalize rows2 id2 = I2 at h ⊢
  generalize codes9 id3 = I9 at h ⊢
  constructor
  · intro hB
    have h1 : Nat.beq (Nat.shiftRight c 36) I2 = true := by rw [hB]; exact Nat.beq_refl _
    rw [h1] at h
    exact Nat.eq_of_beq_eq_true h
  · intro h9
    by_contra hne
    have hf : Nat.beq (Nat.shiftRight c 36) I2 = false :=
      Bool.eq_false_iff.2 fun h' => hne (Nat.eq_of_beq_eq_true h')
    have ht : Nat.beq (fldN c 0 36) I9 = true := by rw [h9]; exact Nat.beq_refl _
    rw [hf, ht] at h
    exact absurd h (by decide)

theorem pair_fact (g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) (hg : g ∈ graphD) :
    encG2 g.1 = rows2 id2 ↔ encG9 g.2 = codes9 id3 := by
  rw [D_eq] at hg
  obtain ⟨k, hk, hgk⟩ := (closD.2.2 dcAll).2 g hg
  have hs := pair_spec DE k (dpAll k hk)
  rwa [← hgk, encGP_hi, encGP_lo] at hs

open CFSG.Quasithin.G2U in
theorem facts : Nat.card rootGroup = 12096 ∧ Nat.card graphD = 6048 ∧
    (∀ g ∈ graphD, g.1 = 1 → g.2 = 1) ∧ (∀ g ∈ graphD, g.2 = 1 → g.1 = 1) := by
  refine ⟨cardR, ?_, fun g hg h1 => ?_, fun g hg h2 => ?_⟩
  · rw [D_eq]
    exact (closD.2.2 dcAll).1
  · have h9 : encG9 g.2 = encG9 1 := by
      rw [one9]
      exact (pair_fact g hg).1 (by rw [h1, one2])
    exact enc9.inj h9
  · have h2' : encG2 g.1 = encG2 1 := by
      rw [one2]
      exact (pair_fact g hg).2 (by rw [h2, one9])
    exact enc2.inj h2'

end CertificateChecks.KernelMisc.G2U

end
