module

public import Certificates.Kernel.MonsterExist.ELevel.Defs
public import Certificates.Kernel.MonsterExist.ShortKey.Lanes
public import Certificates.Kernel.MonsterExist.ShortKey.Short

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ELevel

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.Short CertificateChecks.MonsterExist.ShortKey CertificateChecks.MonsterExist.Eb

noncomputable def pAi (i : ℕ) (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i)) : AutPerm :=
  ⟨decode (cosetArr i), mem_AutPerm_of_arr h1 h2⟩

noncomputable def gAi (i : ℕ) (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i)) : Pvis :=
  ⟨(YU ⟨toC (cosetA i), 0⟩, gO (toC (cosetA i))), YU_gO_mem_Pvis _⟩ *
    ⟨(sU (pAi i h1 h2), PO (pAi i h1 h2)), sU_PO_mem_Pvis _⟩

theorem conjQ_gAi (i : ℕ) (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i))
    (y : Model.Pauli) : conjQ (gAi i h1 h2) (pauliQ y) = pauliQ (alphaN i y) := by
  rw [gAi, conjQ_mul, conjQ_sign_toQ, conjQ_perm_toQ _ (fun k => decode_apply h1 k)]
  rfl

@[expose] def packY (y : Model.Pauli) : ℕ := y.2.1 % 4096 + 4096 * (y.2.2 % 4096) + (if y.1 then 2 ^ 24 else 0)

@[expose] def unpackY (p : ℕ) : Model.Pauli := (p.testBit 24, p % 4096, p / 4096 % 4096)

@[expose] def red (y : Model.Pauli) : Model.Pauli := (y.1, y.2.1 % 4096, y.2.2 % 4096)

theorem pauliQ_red (y : Model.Pauli) : pauliQ (red y) = pauliQ y := by
  rcases y with ⟨s, a, d⟩
  unfold red
  have e : (4096 : ℕ) = 2 ^ 12 := by norm_num
  simp only
  rw [e, pauliQ_mod_d, pauliQ_mod_a]

theorem xmod (a b : ℕ) : (a ^^^ b) % 4096 = a % 4096 ^^^ b % 4096 := by
  have h := Nat.xor_mod_two_pow (a := a) (b := b) (n := 12)
  norm_num at h
  exact h

theorem xdiv (a b : ℕ) : (a ^^^ b) / 4096 = a / 4096 ^^^ b / 4096 := by
  have h := Nat.xor_div_two_pow (a := a) (b := b) (n := 12)
  norm_num at h
  exact h

theorem packY_eq (y : Model.Pauli) :
    packY y = 2 ^ 24 * (if y.1 then 1 else 0) + (y.2.1 % 4096 + 4096 * (y.2.2 % 4096)) := by
  unfold packY
  split_ifs <;> omega

theorem low_lt (a d : ℕ) : a % 4096 + 4096 * (d % 4096) < 2 ^ 24 := by
  have ha := Nat.mod_lt a (show 0 < 4096 by norm_num)
  have hd := Nat.mod_lt d (show 0 < 4096 by norm_num)
  have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  omega

theorem packY_bit (y : Model.Pauli) : (packY y).testBit 24 = y.1 := by
  rw [packY_eq, Nat.testBit_two_pow_mul_add _ (low_lt _ _)]
  cases y.1 <;> simp

theorem packY_mod (y : Model.Pauli) : packY y % 4096 = y.2.1 % 4096 := by
  rw [packY_eq]
  have : (2 : ℕ) ^ 24 = 4096 * 4096 := by norm_num
  rw [this]
  omega

theorem packY_div (y : Model.Pauli) : packY y / 4096 % 4096 = y.2.2 % 4096 := by
  rw [packY_eq]
  have ha := Nat.mod_lt y.2.1 (show 0 < 4096 by norm_num)
  have : (2 : ℕ) ^ 24 = 4096 * 4096 := by norm_num
  rw [this]
  split_ifs <;> omega

theorem unpackY_packY (y : Model.Pauli) : unpackY (packY y) = red y := by
  unfold unpackY red
  rw [packY_bit, packY_mod, packY_div]

theorem packY_lt (y : Model.Pauli) : packY y < 2 ^ 25 := by
  unfold packY
  have ha := Nat.mod_lt y.2.1 (show 0 < 4096 by norm_num)
  have hd := Nat.mod_lt y.2.2 (show 0 < 4096 by norm_num)
  split_ifs <;> omega

theorem mod4096_lt (a : ℕ) : a % 4096 < 2 ^ 12 := by
  have := Nat.mod_lt a (show 0 < 4096 by norm_num)
  norm_num
  exact this

theorem eq_of_pauliQ {x y : Model.Pauli} (h : pauliQ x = pauliQ y) : red x = red y := by
  rw [← pauliQ_red x, ← pauliQ_red y] at h
  exact pauliQ_inj (mod4096_lt _) (mod4096_lt _) (mod4096_lt _) (mod4096_lt _) h

theorem pairN_mod (a d : ℕ) : Model.pairN (a % 4096) (d % 4096) = Model.pairN a d := by
  have h := pairT_eq (a % 4096) (d % 4096)
  have h' := pairT_eq a d
  have e : pairT (a % 4096) (d % 4096) = pairT a d := by
    unfold pairT
    congr 1
    change a % 4096 &&& d % 4096 &&& (2 ^ 12 - 1) = a &&& d &&& (2 ^ 12 - 1)
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one,
      show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow]
    cases decide (i < 12) <;> simp
  rw [e, h'] at h
  cases h1 : Model.pairN (a % 4096) (d % 4096) <;> cases h2 : Model.pairN a d <;> simp_all

theorem unpackY_pmul {p q : ℕ} (hp : p < 2 ^ 25) (hq : q < 2 ^ 25) :
    unpackY (pmul p q) = (unpackY p).mul (unpackY q) ∧ pmul p q < 2 ^ 25 := by
  set t := pairT (Nat.land q (nat_lit 4095)) (Nat.land (Nat.shiftRight p (nat_lit 12)) (nat_lit 4095))
    with ht
  have hn : Nat.land q (nat_lit 4095) = q % 4096 := Nat.and_two_pow_sub_one_eq_mod q 12
  have hn' : Nat.land (Nat.shiftRight p (nat_lit 12)) (nat_lit 4095) = p / 4096 % 4096 := by
    have h := Nat.and_two_pow_sub_one_eq_mod (p >>> 12) 12
    change (p >>> 12) &&& (2 ^ 12 - 1) = _
    rw [h, Nat.shiftRight_eq_div_pow]
  rw [hn, hn', pairT_eq] at ht
  have e : pmul p q = p ^^^ q ^^^ (t <<< 24) := rfl
  have ht2 : t < 2 := by rw [ht]; cases Model.pairN _ _ <;> simp
  have hsh : t <<< 24 < 2 ^ 25 := by
    rw [Nat.shiftLeft_eq]
    have : t * 2 ^ 24 ≤ 1 * 2 ^ 24 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hlt : pmul p q < 2 ^ 25 := by
    rw [e]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hp hq) hsh
  refine ⟨?_, hlt⟩
  have hb : ∀ i, (t <<< 24).testBit i = (decide (i = 24) && t.testBit 0) := by
    intro i
    rw [Nat.testBit_shiftLeft]
    by_cases hi : i = 24
    · subst hi
      simp
    · by_cases hi2 : 24 ≤ i
      · have h2 : (2 : ℕ) ≤ 2 ^ (i - 24) := by
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ i - 24 by omega)
          simpa using this
        have : t.testBit (i - 24) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le ht2 h2)
        simp [hi, hi2, this]
      · simp [hi, hi2]
  unfold unpackY Model.Pauli.mul
  simp only [Model.Pauli.s, Model.Pauli.a, Model.Pauli.d]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    rw [e, Nat.testBit_xor, Nat.testBit_xor, hb, ht]
    simp only [decide_true, Bool.true_and]
    cases Model.pairN (q % 4096) (p / 4096 % 4096) <;> simp
  · simp only
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, e, Nat.testBit_xor, hb]
    by_cases hi : i < 12
    · simp [hi, show i ≠ 24 by omega]
    · simp [hi]
  · simp only
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, e,
      Nat.testBit_xor, hb]
    by_cases hi : i < 12
    · simp [hi, show i + 12 ≠ 24 by omega]
    · simp [hi]

@[expose] noncomputable def pfoldN (B x lo n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun k acc => nIf(Nat.beq (bitN x (Nat.add lo k)) (nat_lit 1), pmul acc (laneW (nat_lit 25) B k), acc)) n

@[expose] noncomputable def xorFoldN (B x lo n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun k acc => Nat.xor acc (selB (bitN x (Nat.add lo k)) (laneW (nat_lit 25) B k))) n

theorem pfold_eq (B x lo : ℕ) : pfold B x lo = pfoldN B x lo 12 := rfl

theorem xorFold_eq (B x lo : ℕ) : xorFold B x lo = xorFoldN B x lo 12 := rfl

theorem bitN_add (x lo k : ℕ) : bitN x (Nat.add lo k) = ((x >>> lo).testBit k).toNat := by
  rw [bitN_eq, Nat.testBit_shiftRight]
  rfl

theorem pfoldN_succ (B x lo n : ℕ) : pfoldN B x lo (n + 1) =
    if (x >>> lo).testBit n then pmul (pfoldN B x lo n) (laneW 25 B n) else pfoldN B x lo n := by
  change nIf(Nat.beq (bitN x (Nat.add lo n)) (nat_lit 1), pmul (pfoldN B x lo n) (laneW (nat_lit 25) B n),
    pfoldN B x lo n) = _
  rw [bitN_add, nIf_eq]
  cases (x >>> lo).testBit n <;> rfl

theorem xorFoldN_succ (B x lo n : ℕ) : xorFoldN B x lo (n + 1) =
    if (x >>> lo).testBit n then xorFoldN B x lo n ^^^ laneW 25 B n else xorFoldN B x lo n := by
  change Nat.xor (xorFoldN B x lo n) (selB (bitN x (Nat.add lo n)) (laneW (nat_lit 25) B n)) = _
  rw [bitN_add, selB_toNat]
  cases (x >>> lo).testBit n
  · exact Nat.xor_zero _
  · rfl

theorem pfoldN_lt (B x lo : ℕ) : ∀ n, pfoldN B x lo n < 2 ^ 25
  | 0 => by change 0 < 2 ^ 25; positivity
  | n + 1 => by
    rw [pfoldN_succ]
    split_ifs
    · exact (unpackY_pmul (pfoldN_lt B x lo n) (laneW_lt _ _)).2
    · exact pfoldN_lt B x lo n

theorem pmul_low (p q : ℕ) : pmul p q % 2 ^ 24 = (p ^^^ q) % 2 ^ 24 := by
  change (p ^^^ q ^^^ (_ <<< 24)) % 2 ^ 24 = _
  rw [Nat.xor_mod_two_pow, Nat.shiftLeft_eq, Nat.mul_mod_left, Nat.xor_zero]

theorem pfoldN_low (B x lo : ℕ) : ∀ n, pfoldN B x lo n % 2 ^ 24 = xorFoldN B x lo n % 2 ^ 24
  | 0 => rfl
  | n + 1 => by
    rw [pfoldN_succ, xorFoldN_succ]
    split_ifs
    · rw [pmul_low, Nat.xor_mod_two_pow, pfoldN_low B x lo n, ← Nat.xor_mod_two_pow]
    · exact pfoldN_low B x lo n

theorem mod_succ_xor (y n : ℕ) :
    y % 2 ^ (n + 1) = if y.testBit n then y % 2 ^ n ^^^ 2 ^ n else y % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  split_ifs with h
  · rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hi : i < n
    · simp [hi, show i < n + 1 by omega, show n ≠ i by omega]
    · by_cases hi2 : i = n
      · subst hi2
        simp [h]
      · simp [hi, show ¬ i < n + 1 by omega, show n ≠ i by omega]
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < n
    · simp [hi, show i < n + 1 by omega]
    · by_cases hi2 : i = n
      · subst hi2
        simp [h]
      · simp [hi, show ¬ i < n + 1 by omega]

theorem unpackY_zero : unpackY 0 = (false, 0, 0) := by
  simp only [unpackY, Nat.zero_testBit, Nat.zero_mod, Nat.zero_div]

theorem pfoldN_pauliQ (i : ℕ) (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i))
    (B lo : ℕ) (emb : ℕ → Model.Pauli) (hemb : ∀ m m', (emb m).mul (emb m') = emb (m ^^^ m'))
    (hemb0 : emb 0 = (false, 0, 0))
    (hB : ∀ k < 12, laneW 25 B k = packY (alphaN i (emb (2 ^ k)))) (x : ℕ) :
    ∀ n ≤ 12, pauliQ (unpackY (pfoldN B x lo n)) = pauliQ (alphaN i (emb ((x >>> lo) % 2 ^ n)))
  | 0, _ => by
    have e0 : pfoldN B x lo 0 = 0 := rfl
    have e1 : (x >>> lo) % 2 ^ 0 = 0 := Nat.mod_one _
    rw [e0, e1, unpackY_zero, pauliQ_false_zero, hemb0, ← conjQ_gAi i h1 h2 (false, 0, 0),
      pauliQ_false_zero, map_one]
  | n + 1, hn => by
    have ih := pfoldN_pauliQ i h1 h2 B lo emb hemb hemb0 hB x n (by omega)
    have hm := mod_succ_xor (x >>> lo) n
    rw [pfoldN_succ, hm]
    by_cases hbit : (x >>> lo).testBit n = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hbit), ite_eq_left_of_eq_true _ _ (eq_true hbit)]
      have hl : pauliQ (unpackY (laneW 25 B n)) = pauliQ (alphaN i (emb (2 ^ n))) := by
        rw [hB n (by omega), unpackY_packY, pauliQ_red]
      have hp := (unpackY_pmul (pfoldN_lt B x lo n) (laneW_lt (W := 25) B n)).1
      calc pauliQ (unpackY (pmul (pfoldN B x lo n) (laneW 25 B n)))
          = pauliQ (unpackY (pfoldN B x lo n)) * pauliQ (unpackY (laneW 25 B n)) := by
            rw [hp]
            exact pauliQ_mul _ _
        _ = pauliQ (alphaN i (emb ((x >>> lo) % 2 ^ n))) * pauliQ (alphaN i (emb (2 ^ n))) := by
            rw [ih, hl]
        _ = conjQ (gAi i h1 h2) (pauliQ (emb ((x >>> lo) % 2 ^ n))) *
              conjQ (gAi i h1 h2) (pauliQ (emb (2 ^ n))) := by
            rw [conjQ_gAi i h1 h2 (emb ((x >>> lo) % 2 ^ n)), conjQ_gAi i h1 h2 (emb (2 ^ n))]
        _ = conjQ (gAi i h1 h2) (pauliQ ((emb ((x >>> lo) % 2 ^ n)).mul (emb (2 ^ n)))) :=
            ((congrArg (conjQ (gAi i h1 h2)) (pauliQ_mul (emb ((x >>> lo) % 2 ^ n)) (emb (2 ^ n)))).trans
              (map_mul (conjQ (gAi i h1 h2)) _ _)).symm
        _ = conjQ (gAi i h1 h2) (pauliQ (emb ((x >>> lo) % 2 ^ n ^^^ 2 ^ n))) :=
            congrArg (fun m => conjQ (gAi i h1 h2) (pauliQ m)) (hemb _ _)
        _ = pauliQ (alphaN i (emb ((x >>> lo) % 2 ^ n ^^^ 2 ^ n))) := conjQ_gAi i h1 h2 _
    · have hbit' : ((x >>> lo).testBit n = true) = False := by simpa using hbit
      rw [ite_eq_right_of_eq_false _ _ hbit', ite_eq_right_of_eq_false _ _ hbit']
      exact ih

@[expose] def embT (m : ℕ) : Model.Pauli := (false, m, 0)

@[expose] def embD (m : ℕ) : Model.Pauli := (false, 0, m)

theorem pairN_zero_right (a : ℕ) : Model.pairN a 0 = false := by
  unfold Model.pairN
  rw [Nat.and_zero]
  rfl

theorem pairN_zero_left (d : ℕ) : Model.pairN 0 d = false := by
  unfold Model.pairN
  rw [Nat.zero_and]
  rfl

theorem embT_mul (m m' : ℕ) : (embT m).mul (embT m') = embT (m ^^^ m') := by
  unfold embT Model.Pauli.mul
  simp [pairN_zero_right]

theorem embD_mul (m m' : ℕ) : (embD m).mul (embD m') = embD (m ^^^ m') := by
  unfold embD Model.Pauli.mul
  simp [pairN_zero_left]

@[expose] def BasisOK (i TB DB : ℕ) : Prop :=
  ∀ k < 12, laneW 25 TB k = packY (alphaN i (false, 2 ^ k, 0)) ∧
    laneW 25 DB k = packY (alphaN i (false, 0, 2 ^ k))

theorem red_unpackY (p : ℕ) : red (unpackY p) = unpackY p := by
  unfold red unpackY
  simp only [Nat.mod_mod]

theorem kapL_eq (TB DB x : ℕ) : kapL TB DB x = (pfold TB x 0 ^^^ pfold DB x 12) % 2 ^ 24 := by
  unfold kapL
  change (xorFold TB x 0 ^^^ xorFold DB x 12) &&& (2 ^ 24 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.xor_mod_two_pow, xorFold_eq, xorFold_eq,
    ← pfoldN_low, ← pfoldN_low, ← pfold_eq, ← pfold_eq, ← Nat.xor_mod_two_pow]

theorem split24 (z : ℕ) : z % 2 ^ 24 = z % 4096 + 4096 * (z / 4096 % 4096) := by
  have : (2 : ℕ) ^ 24 = 4096 * 4096 := by norm_num
  rw [this]
  omega

section Basis

variable {i TB DB : ℕ} (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i))
  (hb : BasisOK i TB DB)
include h1 h2 hb

theorem tT_red (x : ℕ) : red ((tT i)[x % 4096]!) = unpackY (pfold TB x 0) := by
  rw [tT_get i (A := x % 4096) (mod4096_lt x)]
  have h := pfoldN_pauliQ i h1 h2 TB 0 embT embT_mul rfl (fun k hk => (hb k hk).1) x 12 le_rfl
  have e : (x >>> 0) % 2 ^ 12 = x % 4096 := by rw [Nat.shiftRight_zero]; norm_num
  rw [e] at h
  rw [pfold_eq, ← red_unpackY]
  exact (eq_of_pauliQ h).symm

theorem tD_red (x : ℕ) : red ((tD i)[(x >>> 12) % 4096]!) = unpackY (pfold DB x 12) := by
  rw [tD_get i (D := (x >>> 12) % 4096) (mod4096_lt _)]
  have h := pfoldN_pauliQ i h1 h2 DB 12 embD embD_mul rfl (fun k hk => (hb k hk).2) x 12 le_rfl
  have e : (x >>> 12) % 2 ^ 12 = (x >>> 12) % 4096 := by norm_num
  rw [e] at h
  rw [pfold_eq, ← red_unpackY]
  exact (eq_of_pauliQ h).symm

theorem kapX_eq_kapL (x : ℕ) : kapX (tT i) (tD i) x = kapL TB DB x := by
  have ht := tT_red h1 h2 hb x
  have hd := tD_red h1 h2 hb x
  unfold red unpackY at ht hd
  simp only [Prod.mk.injEq] at ht hd
  have hk : kapX (tT i) (tD i) x =
      ((tT i)[x % 4096]!.2.1 ^^^ (tD i)[(x >>> 12) % 4096]!.2.1) % 4096 +
        4096 * (((tT i)[x % 4096]!.2.2 ^^^ (tD i)[(x >>> 12) % 4096]!.2.2) % 4096) := rfl
  rw [hk, kapL_eq TB DB x, split24, xmod, xmod, ht.2.1, hd.2.1, ht.2.2, hd.2.2, xmod, xdiv, xmod]

theorem csX_eq_csK (x : ℕ) : csX (tT i) (tD i) x = (csK TB DB x == 1) := by
  have ht := tT_red h1 h2 hb x
  have hd := tD_red h1 h2 hb x
  have hp := (unpackY_pmul (pfoldN_lt TB x 0 12) (pfoldN_lt DB x 12 12)).1
  rw [← pfold_eq, ← pfold_eq] at hp
  have hc : csK TB DB x = ((unpackY (pmul (pfold TB x 0) (pfold DB x 12))).1).toNat := by
    unfold csK
    rw [bitN_eq]
    rfl
  rw [hc, hp, ← ht, ← hd]
  have e : csX (tT i) (tD i) x = ((tT i)[x % 4096]!.mul (tD i)[(x >>> 12) % 4096]!).1 := rfl
  rw [e]
  unfold red Model.Pauli.mul
  simp only [Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_mod]
  cases ((tT i)[x % 4096]!.1 ^^ (tD i)[(x >>> 12) % 4096]!.1 ^^
    Model.pairN (tD i)[(x >>> 12) % 4096]!.2.1 (tT i)[x % 4096]!.2.2) <;> rfl

end Basis

end CertificateChecks.MonsterExist.ELevel

end
