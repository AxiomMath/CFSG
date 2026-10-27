module

public import Certificates.Data.Kernel.J4NP7850
public import CFSG.Certificates.Kernel.J4Q.WordVJ
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Sporadic.J4.Action
public import CFSG.Sporadic.J4.QT2LocCntGen
public import Certificates.Kernel.J4Q.Mat

@[expose] public section

namespace CertificateChecks.KernelJ4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4M4F CFSG.KD.J4NP7850 CFSG.Sporadic.J4
  CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.KS.PackFld

@[expose] noncomputable def rowN (x : Nat) : Row := toRow (ofN x).toVec

theorem bit_mul (x k : Nat) : (x >>> k) &&& 1 = if x.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x >>> k) with h | h <;> rw [h] <;> rfl

theorem xsum_xor (f g : Nat → Nat) : ∀ n, xsum (fun k => f k ^^^ g k) n = xsum f n ^^^ xsum g n
  | 0 => by
    change (0 : Nat) = 0 ^^^ 0
    rw [Nat.zero_xor]
  | n + 1 => by
    rw [xsum_succ, xsum_succ, xsum_succ, xsum_xor f g n]
    simp only [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

theorem xsum_lt7850 {f : Nat → Nat} {m : Nat} : ∀ {n : Nat}, (∀ k < n, f k < 2 ^ m) →
    xsum f n < 2 ^ m
  | 0, _ => Nat.two_pow_pos m
  | n + 1, h => by
    rw [xsum_succ]
    exact Nat.xor_lt_two_pow (xsum_lt7850 fun k hk => h k (by omega)) (h n (by omega))

theorem strictN_eq7850 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem getN_eq7850 (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_eq7850 d l i

theorem rm_eq7850 : rm = 2 ^ 112 - 1 := (consts_c hK).2

theorem testBit_rowJ7850 (M r j : Nat) :
    (rowJ rm M r).testBit j = (M.testBit (r * 128 + j) && decide (j < 112)) := by
  rw [rm_eq7850]
  change ((M >>> (r * 128)) &&& (2 ^ 112 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]

theorem rowJ_lt7850 (M r : Nat) : rowJ rm M r < 2 ^ 112 := by
  rw [rm_eq7850]
  exact Nat.and_lt_two_pow _ (by omega)

theorem and_rm7850 {y : Nat} (hy : y < 2 ^ 112) : y &&& rm = y := by
  rw [rm_eq7850]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow hy

theorem rowJ_xor7850 (A B r : Nat) : rowJ rm (A ^^^ B) r = rowJ rm A r ^^^ rowJ rm B r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_rowJ7850, testBit_rowJ7850, testBit_rowJ7850, Nat.testBit_xor]
  cases decide (j < 112) <;> simp

theorem vecJ_xor (a b M : Nat) : vecJ rm (a ^^^ b) M = vecJ rm a M ^^^ vecJ rm b M := by
  rw [vecJ_eq, vecJ_eq, vecJ_eq, ← xsum_xor]
  apply xsum_congr
  intro k _
  rw [bit_mul, bit_mul, bit_mul, Nat.testBit_xor]
  cases a.testBit k <;> cases b.testBit k <;> simp

theorem vecJ_zero (M : Nat) : vecJ rm 0 M = 0 := by
  rw [vecJ_eq]
  apply xsum_zero
  intro k _
  rw [bit_mul, Nat.zero_testBit]
  simp

theorem vecJ_xorM (x A B : Nat) : vecJ rm x (A ^^^ B) = vecJ rm x A ^^^ vecJ rm x B := by
  rw [vecJ_eq, vecJ_eq, vecJ_eq, ← xsum_xor]
  apply xsum_congr
  intro k _
  rw [rowJ_xor7850, bit_mul]
  split <;> simp

theorem vecJ_xsum (b : Nat) (f : Nat → Nat) : ∀ n, vecJ rm (xsum f n) b = xsum (fun i => vecJ rm (f i) b) n
  | 0 => vecJ_zero b
  | n + 1 => by rw [xsum_succ, xsum_succ, vecJ_xor, vecJ_xsum b f n]

@[expose] noncomputable def bsum7850 (h : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc + h i * 2 ^ (128 * i)) n

theorem bsum7850_succ (h : Nat → Nat) (n : Nat) :
    bsum7850 h (n + 1) = bsum7850 h n + h n * 2 ^ (128 * n) := rfl

theorem fld_bsum7850 {h : Nat → Nat} (hh : ∀ i, h i < 2 ^ 128) : ∀ n,
    Fld 128 (bsum7850 h n) (fun i => if i < n then h i else 0) ∧ bsum7850 h n < 2 ^ (128 * n)
  | 0 => ⟨fld_congr (fld_zero 128) (fun i => by simp), by simp [bsum7850]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := fld_bsum7850 hh n
    have e : bsum7850 h (n + 1) = h n <<< (128 * n) ||| bsum7850 h n := by
      rw [bsum7850_succ, Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt ih2]
    refine ⟨?_, ?_⟩
    · rw [e]
      refine fld_congr (fld_or (fld_shl n (fld_one (hh n))) ih1) ?_
      intro i
      by_cases h1 : i < n
      · have h2 : ¬ n ≤ i := by omega
        have h3 : i < n + 1 := by omega
        simp [h1, h2, h3]
      · by_cases h2 : i = n
        · subst h2
          simp
        · have h3 : ¬ i < n + 1 := by omega
          have h4 : ¬ i - n = 0 := by omega
          simp [h1, h3, h4]
    · rw [bsum7850_succ]
      have h3 : h n * 2 ^ (128 * n) + 2 ^ (128 * n) ≤ 2 ^ 128 * 2 ^ (128 * n) := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (hh n)
      rw [Nat.mul_succ, Nat.add_comm (128 * n) 128, Nat.pow_add]
      omega

theorem bsum7850_mul (h : Nat → Nat) (v : Nat) :
    ∀ n, bsum7850 h n * v = bsum7850 (fun i => h i * v) n
  | 0 => by simp [bsum7850]
  | n + 1 => by
    rw [bsum7850_succ, bsum7850_succ, Nat.add_mul, bsum7850_mul h v n, Nat.mul_right_comm]

theorem fld_eq7850 {w X Y : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
    (hY : Fld w Y g) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hd := Nat.div_add_mod p w
  rw [← hd, hX _ _ (Nat.mod_lt _ hw), hY _ _ (Nat.mod_lt _ hw)]

theorem fld_xor7850 {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ^^^ B) (fun i => g i ^^^ h i) := by
  intro i k hk
  rw [Nat.testBit_xor, hA i k hk, hB i k hk, Nat.testBit_xor]

theorem fld_and7850 {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A &&& B) (fun i => g i &&& h i) := by
  intro i k hk
  rw [Nat.testBit_and, hA i k hk, hB i k hk, Nat.testBit_and]

theorem fld_xsum7850 {P : Nat → Nat} {G : Nat → Nat → Nat} : ∀ {n : Nat},
    (∀ k < n, Fld 128 (P k) (G k)) → Fld 128 (xsum P n) (fun i => xsum (fun k => G k i) n)
  | 0, _ => fld_congr (fld_zero 128) (fun _ => rfl)
  | n + 1, h => fld_congr (fld_xor7850 (fld_xsum7850 (fun k hk => h k (by omega))) (h n (by omega)))
      (fun _ => rfl)

theorem c_bsum7850 : c = bsum7850 (fun _ => 1) 112 :=
  Nat.eq_of_beq_eq_true (by decide +kernel)

@[expose] noncomputable def step7850 (a b k : Nat) : Nat :=
  ((a >>> k) &&& c) * rm &&& ((b >>> (k * 128)) &&& rm) * c

theorem mrec7850 (a b : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => mstep c rm a b acc k) n = xsum (step7850 a b) n
  | 0 => rfl
  | n + 1 => by
    change mstep c rm a b (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => mstep c rm a b acc k) n) n = _
    rw [mrec7850 a b n]
    rfl

theorem mulJ_eq7850 (a b : Nat) : mulJ c rm a b = xsum (step7850 a b) 112 := by
  unfold mulJ
  rw [strictN_eq7850, strictN_eq7850]
  exact mrec7850 a b 112

theorem fld_step7850 (a b : Nat) {k : Nat} (hk : k < 112) :
    Fld 128 (step7850 a b k)
      (fun i => if i < 112 then (if a.testBit (128 * i + k) then rowJ rm b k else 0) else 0) := by
  have hc := (fld_bsum7850 (h := fun _ => 1) (fun _ => by omega) 112).1
  rw [← c_bsum7850] at hc
  have hx : Fld 128 ((a >>> k) &&& c)
      (fun i => if i < 112 then (if a.testBit (128 * i + k) then 1 else 0) else 0) := by
    intro i j hj
    rw [Nat.testBit_and, Nat.testBit_shiftRight, hc i j hj]
    by_cases hi : i < 112
    · simp only [hi, ↓reduceIte]
      by_cases hj0 : j = 0
      · subst hj0
        have e : k + (128 * i + 0) = 128 * i + k := by omega
        rw [e]
        cases a.testBit (128 * i + k) <;> simp
      · have h1 : (1 : Nat).testBit j = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hj0)
        cases a.testBit (128 * i + k) <;> simp [h1]
    · simp [hi]
  have hxe := fld_eq7850 (by omega : 0 < 128) hx
    (fld_bsum7850 (h := fun i : Nat => if a.testBit (128 * i + k) then 1 else 0)
      (fun i => by split <;> omega) 112).1
  have hy : (b >>> (k * 128)) &&& rm = rowJ rm b k := rfl
  have hyl := rowJ_lt7850 b k
  have hxb : ∀ i : Nat, (if a.testBit (128 * i + k) then 1 else 0) * rm < 2 ^ 128 := by
    intro i
    rw [rm_eq7850]
    split
    · rw [Nat.one_mul]
      exact Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos 112) Nat.one_pos)
        (Nat.pow_le_pow_right (by omega) (by omega))
    · rw [Nat.zero_mul]
      exact Nat.two_pow_pos 128
  have h1 : Fld 128 (((a >>> k) &&& c) * rm)
      (fun i => if i < 112 then (if a.testBit (128 * i + k) then 1 else 0) * rm else 0) := by
    rw [hxe, bsum7850_mul]
    exact (fld_bsum7850 hxb 112).1
  have h2 : Fld 128 (rowJ rm b k * c) (fun i => if i < 112 then 1 * rowJ rm b k else 0) := by
    rw [c_bsum7850, Nat.mul_comm (rowJ rm b k), bsum7850_mul]
    exact (fld_bsum7850 (fun _ => by
      simp only [Nat.one_mul]
      exact Nat.lt_of_lt_of_le hyl (Nat.pow_le_pow_right (by omega) (by omega))) 112).1
  unfold step7850
  rw [hy]
  refine fld_congr (fld_and7850 h1 h2) ?_
  intro i
  by_cases hi : i < 112
  · simp only [hi, ↓reduceIte]
    cases a.testBit (128 * i + k)
    · simp
    · simp only [↓reduceIte, Nat.one_mul]
      rw [Nat.and_comm, and_rm7850 hyl]
  · simp [hi]

theorem rowJ_mulJ7850 (a b : Nat) {i : Nat} (hi : i < 112) :
    rowJ rm (mulJ c rm a b) i = vecJ rm (rowJ rm a i) b := by
  have hF : Fld 128 (mulJ c rm a b) (fun i => xsum (fun k => if i < 112 then
      (if a.testBit (128 * i + k) then rowJ rm b k else 0) else 0) 112) := by
    rw [mulJ_eq7850]
    exact fld_xsum7850 (fun k hk => fld_step7850 a b hk)
  have hR : vecJ rm (rowJ rm a i) b =
      xsum (fun k => if a.testBit (128 * i + k) then rowJ rm b k else 0) 112 := by
    rw [vecJ_eq]
    apply xsum_congr
    intro k hk
    rw [bit_mul, testBit_rowJ7850, Nat.mul_comm i 128]
    simp only [hk, decide_true, Bool.and_true]
    cases a.testBit (128 * i + k) <;> simp
  rw [hR]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowJ7850]
  by_cases hj : j < 112
  · rw [Nat.mul_comm i 128, hF i j (by omega)]
    simp only [hj, hi, decide_true, Bool.and_true, ↓reduceIte]
  · simp only [hj, decide_false, Bool.and_false]
    have hl : xsum (fun k => if a.testBit (128 * i + k) then rowJ rm b k else 0) 112 < 2 ^ 112 :=
      xsum_lt7850 fun k _ => by
        split
        · exact rowJ_lt7850 b k
        · exact Nat.two_pow_pos 112
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by omega)
      (by omega)))).symm

theorem vecJ_mulJ_any (x a b : Nat) : vecJ rm x (mulJ c rm a b) = vecJ rm (vecJ rm x a) b := by
  rw [vecJ_eq rm x a, vecJ_xsum, vecJ_eq rm x (mulJ c rm a b)]
  apply xsum_congr
  intro i hi
  rw [rowJ_mulJ7850 a b hi, bit_mul]
  split
  · rw [Nat.one_mul, Nat.one_mul]
  · rw [Nat.zero_mul, Nat.zero_mul, vecJ_zero]

theorem vecJ_one7850 {v : Nat} (hv : v < 2 ^ 112) : vecJ rm v one = v := by
  obtain ⟨hw, he⟩ := id_enc hK
  rw [← he, ← ofN_eq hv, ← v2N_frApply hK hw (wf_ofN hv), frApply_idRows4204 (wf_ofN hv)]

theorem qrow_bit7850 (M : Nat) {k j : Nat} (hj : j < 112) : ∀ P : List Nat, k ∉ P →
    (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun p _ ih => Nat.lor ih (Nat.shiftLeft (rowJ rm M p) (Nat.mul (nat_lit 128) p))) P).testBit
        (k * 128 + j) = false
  | [], _ => Nat.zero_testBit _
  | p :: P, hk => by
    have hkp : k ≠ p := fun e => hk (by simp [e])
    have hkP : k ∉ P := fun h => hk (by simp [h])
    change (Nat.lor _ (Nat.shiftLeft (rowJ rm M p) (Nat.mul 128 p))).testBit (k * 128 + j) = false
    rw [Nat.lor_eq, Nat.testBit_or, qrow_bit7850 M hj P hkP, Bool.false_or, Nat.shiftLeft_eq',
      Nat.testBit_shiftLeft]
    by_cases h : k < p
    · have : ¬ 128 * p ≤ k * 128 + j := by omega
      simp [this]
    · have : ¬ (k * 128 + j - 128 * p < 112) := by omega
      rw [testBit_rowJ7850]
      simp [this]

theorem rowJ_q7850 {P : List Nat} {Q : Nat} (hq : qK rm P Q = true) {k : Nat} (hk : k ∉ P) :
    rowJ rm Q k = 0 := by
  have hQ := Nat.eq_of_beq_eq_true hq
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowJ7850, Nat.zero_testBit]
  by_cases hj : j < 112
  · rw [← hQ, qrow_bit7850 Q hj P hk, Bool.false_and]
  · simp [hj]

theorem vecJ_q7850 {P : List Nat} {Q : Nat} (hq : qK rm P Q = true) {v : Nat}
    (hP : ∀ p ∈ P, v.testBit p = false) : vecJ rm v Q = 0 := by
  rw [vecJ_eq]
  apply xsum_zero
  intro k _
  by_cases hk : k ∈ P
  · rw [bit_mul, hP k hk]
    simp
  · rw [rowJ_q7850 hq hk, Nat.mul_zero]

theorem rec_succ7850 (Q : Nat) (F : Nat → Nat → Nat) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) Q F (n + 1) = F n (Nat.rec (motive := fun _ => Nat) Q F n) :=
  rfl

theorem rank_loop7850{FM R : List Nat} {Q v : Nat} (hv : v < 2 ^ 112)
    (hfix : ∀ j < 10, vecJ rm v (FM.getD j one) = v) : ∀ n ≤ 10,
    vecJ rm v (Nat.rec (motive := fun _ => Nat) Q (fun j acc => strictN acc fun a => a ^^^
      mulJ c rm (getN one FM j ^^^ one) (getN 0 R j)) n) = vecJ rm v Q
  | 0, _ => rfl
  | n + 1, hn => by
    refine Eq.trans (congrArg (vecJ rm v) (rec_succ7850 _ _ n)) ?_
    beta_reduce
    rw [strictN_eq7850]
    beta_reduce
    rw [vecJ_xorM, rank_loop7850 hv hfix n (by omega), vecJ_mulJ_any, vecJ_xorM,
      getN_eq7850 one FM n, hfix n (by omega), vecJ_one7850 hv, Nat.xor_self, vecJ_zero,
      Nat.xor_zero]

theorem rankK_spec {FM R P : List Nat} {Q : Nat} (hrank : rankK c rm one FM R Q = true)
    (hq : qK rm P Q = true) {v : Nat} (hv : v < 2 ^ 112)
    (hfix : ∀ j < 10, vecJ rm v (FM.getD j one) = v) (hP : ∀ p ∈ P, v.testBit p = false) :
    v = 0 := by
  have h1 := Nat.eq_of_beq_eq_true hrank
  have h2 := rank_loop7850 (R := R) (Q := Q) hv hfix 10 le_rfl
  rw [← vecJ_one7850 hv, ← h1]
  exact h2.trans (vecJ_q7850 hq hP)

end CertificateChecks.KernelJ4NP7850

end
