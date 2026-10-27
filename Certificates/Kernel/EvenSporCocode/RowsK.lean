module

public import Certificates.Kernel.EvenSporCocode.Data
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CertificateChecks.KernelCocode

open CFSG.KC.EvenSporCocode CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

@[expose] noncomputable def strictRB (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def mask120R : ℕ := 1329227995784915872903807060280344575

@[expose] noncomputable def digRw (X i : ℕ) : ℕ := Nat.land (Nat.shiftRight X (Nat.mul 5 i)) 31

@[expose] noncomputable def hornerR (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ acc => Nat.add x (Nat.mul acc 32)) l

@[expose] noncomputable def tmulGen (d : ℕ → ℕ) : ℕ :=
  Nat.add (d 0) (Nat.mul (Nat.add (d 1) (Nat.mul (Nat.add (d 2) (Nat.mul (Nat.add (d 3) (Nat.mul
  (Nat.add (d 4) (Nat.mul (Nat.add (d 5) (Nat.mul (Nat.add (d 6) (Nat.mul (Nat.add (d 7) (Nat.mul
  (Nat.add (d 8) (Nat.mul (Nat.add (d 9) (Nat.mul (Nat.add (d 10) (Nat.mul (Nat.add (d 11)
  (Nat.mul (Nat.add (d 12) (Nat.mul (Nat.add (d 13) (Nat.mul (Nat.add (d 14) (Nat.mul (Nat.add
  (d 15) (Nat.mul (Nat.add (d 16) (Nat.mul (Nat.add (d 17) (Nat.mul (Nat.add (d 18) (Nat.mul
  (Nat.add (d 19) (Nat.mul (Nat.add (d 20) (Nat.mul (Nat.add (d 21) (Nat.mul (Nat.add (d 22)
  (Nat.mul (Nat.add (d 23) (Nat.mul 0 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32))
  32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)) 32)

@[expose] noncomputable def digPR (S T i : ℕ) : ℕ := digRw S (digRw T i)

@[expose] noncomputable def tmulR (S T : ℕ) : ℕ := tmulGen (digPR S T)

@[expose] noncomputable def colRw (EP T U R : ℕ) : Bool :=
  Nat.beq (tmulR T U) (Nat.land (Nat.shiftRight EP (Nat.mul 120 (Nat.land R 1023))) mask120R)

@[expose] noncomputable def rowGoG (c : ℕ → ℕ → Bool) (Us : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun U _ ih R => Bool.rec false (ih (Nat.shiftRight R 10)) (c U R)) Us

@[expose] noncomputable def ivMemR (i : ℕ) (IV : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun v _ ih => Bool.rec ih true (Nat.beq v i)) IV

@[expose] noncomputable def mask10240R : ℕ := Nat.sub (Nat.shiftLeft 1 10240) 1

@[expose] noncomputable def rowsAtR (EP : ℕ) (RB IV K : List ℕ) (i : ℕ) : Bool :=
  Bool.rec (zeroSeg RB i)
    (strictRB (K.getD i 0) fun T =>
      strictRB (Nat.land (Nat.shiftRight (RB.getD (i / 32) 0) (Nat.mul 10240 (i % 32)))
        mask10240R) fun R => rowGoG (colRw EP T) K R)
    (ivMemR i IV)

@[expose] noncomputable def rowCR (i : ℕ) : Bool := rowsAtR D.EP D.RB D.IV D.KT i

theorem strictRB_eq (y : ℕ) (k : ℕ → Bool) : strictRB y k = k y := by
  cases y <;> rfl

theorem boolRec_falseR (a b : Bool) : Bool.rec (motive := fun _ => Bool) false a b = (b && a) := by
  cases b <;> rfl

theorem boolRec_trueR (a b : Bool) : Bool.rec (motive := fun _ => Bool) a true b = (b || a) := by
  cases b <;> rfl

theorem digRw_eq (X i : ℕ) : digRw X i = dig X i := by
  change (X >>> (5 * i)) &&& (2 ^ 5 - 1) = (X >>> (5 * i)) % 2 ^ 5
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem hornerR_eq : ∀ l : List ℕ, hornerR l = encT l
  | [] => rfl
  | x :: l => by
    have e : hornerR (x :: l) = x + hornerR l * 32 := rfl
    rw [e, hornerR_eq l]
    simp only [encT, List.foldr_cons]

theorem tmulGen_eq (d : ℕ → ℕ) : tmulGen d = encT ((List.range 24).map d) := by
  have e : tmulGen d = hornerR [d 0, d 1, d 2, d 3, d 4, d 5, d 6, d 7, d 8, d 9, d 10, d 11,
      d 12, d 13, d 14, d 15, d 16, d 17, d 18, d 19, d 20, d 21, d 22, d 23] := rfl
  rw [e, hornerR_eq]
  rfl

theorem segMod_R (X b : ℕ) (hb : b + 10 ≤ 10240) :
    ((X % 2 ^ 10240) >>> b) % 2 ^ 10 = (X >>> b) % 2 ^ 10 := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hk : k < 10
  · have : b + k < 10240 := by omega
    simp [hk, this]
  · simp [hk]

theorem landMask_eqR (X n : ℕ) : Nat.land X (Nat.sub (Nat.shiftLeft 1 n) 1) = X % 2 ^ n := by
  change X &&& ((1 <<< n) - 1) = _
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem mask10240R_eq (X : ℕ) : Nat.land X mask10240R = X % 2 ^ 10240 := landMask_eqR X 10240

theorem tmulR_eq (S T : ℕ) : tmulR S T = tmulK S T := by
  rw [tmulR, tmulGen_eq, tmulK]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [digPR, digRw_eq, digRw_eq]

theorem fld_eq (EP k : ℕ) :
    Nat.land (Nat.shiftRight EP (Nat.mul 120 k)) mask120R = fldE EP k := by
  have : mask120R = 2 ^ 120 - 1 := by norm_num [mask120R]
  rw [this]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem rowGoG_cons (c : ℕ → ℕ → Bool) (U : ℕ) (Us : List ℕ) (R : ℕ) :
    rowGoG c (U :: Us) R = (c U R && rowGoG c Us (Nat.shiftRight R 10)) :=
  boolRec_falseR (rowGoG c Us (Nat.shiftRight R 10)) (c U R)

theorem rowGoR_spec (EP : ℕ) (RB : List ℕ) (i T : ℕ) :
    ∀ (Us : List ℕ) (j R : ℕ),
      R = ((RB.getD (i / 32) 0 >>> (10240 * (i % 32))) % 2 ^ 10240) >>> (10 * j) →
      j + Us.length ≤ 1024 → rowGoG (colRw EP T) Us R = true → rowGo EP RB i T Us j = true
  | [], _, _, _, _, _ => by rw [rowGo]
  | U :: Us, j, R, hR, hl, h => by
    rw [rowGoG_cons, Bool.and_eq_true, colRw] at h
    have hj : j < 1024 := by simp at hl; omega
    have e1 := Nat.eq_of_beq_eq_true h.1
    have hlk : Nat.land R 1023 = lookK RB i j := by
      have e2 : Nat.land R 1023 = R % 2 ^ 10 := Nat.and_two_pow_sub_one_eq_mod _ 10
      rw [e2, hR, segMod_R _ _ (by omega), lookK, if_pos hj,
        show 10 * (1024 * (i % 32) + j) = 10240 * (i % 32) + 10 * j by ring, Nat.shiftRight_add]
      try rfl
    rw [hlk, fld_eq, tmulR_eq] at e1
    have h2 : Nat.shiftRight R 10 =
        ((RB.getD (i / 32) 0 >>> (10240 * (i % 32))) % 2 ^ 10240) >>> (10 * (j + 1)) := by
      change R >>> 10 = _
      rw [hR, ← Nat.shiftRight_add, show 10 * j + 10 = 10 * (j + 1) by ring]
    have ih := rowGoR_spec EP RB i T Us (j + 1) _ h2 (by simp at hl; omega) h.2
    rw [rowGo, Bool.and_eq_true, beq_iff_eq]
    exact ⟨e1, ih⟩

theorem ivMemR_eq (i : ℕ) : ∀ IV : List ℕ, ivMemR i IV = IV.contains i
  | [] => rfl
  | v :: vs => by
    have ih := ivMemR_eq i vs
    have e : ivMemR i (v :: vs) = (Nat.beq v i || ivMemR i vs) :=
      boolRec_trueR (ivMemR i vs) (Nat.beq v i)
    rw [e, List.contains_cons, ih]
    by_cases h : v = i
    · subst h
      simp
    · have : Nat.beq v i = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact h (Nat.eq_of_beq_eq_true hc)
      rw [this]
      simp [Ne.symm h]

theorem rowsAt_of_R {EP : ℕ} {RB IV K : List ℕ} {L : List (List ℕ)} (hiv : invsK L = IV)
    (hK : K.length ≤ 1024) {i : ℕ} (hi : i < 1024) (h : rowsAtR EP RB IV K i = true) :
    rowsAt EP RB L K i = true := by
  have hm : ivMemR i IV = isInv (L.getD i []) := by
    rw [ivMemR_eq, ← hiv, invsK]
    by_cases hv : isInv (L.getD i []) = true
    · rw [hv]
      exact List.contains_iff_mem.2 (List.mem_filter.2 ⟨List.mem_range.2 hi, hv⟩)
    · rw [Bool.not_eq_true] at hv
      rw [hv, Bool.eq_false_iff]
      intro hc
      have := (List.mem_filter.1 (List.contains_iff_mem.1 hc)).2
      rw [hv] at this
      exact Bool.false_ne_true this
  rw [rowsAtR, hm] at h
  rw [rowsAt]
  cases hc : isInv (L.getD i []) with
  | false =>
    rw [hc] at h
    rw [if_neg Bool.false_ne_true]
    exact h
  | true =>
    rw [hc] at h
    change strictRB _ _ = true at h
    simp only [strictRB_eq] at h
    rw [if_pos rfl]
    refine rowGoR_spec EP RB i _ K 0 _ ?_ (by omega) h
    rw [Nat.mul_zero, Nat.shiftRight_zero, mask10240R_eq]
    try rfl

theorem rows_of_rowCR (hiv : invsK D.LT = D.IV) (hK : D.KT.length ≤ 1024)
    (h : ∀ i < 1024, rowCR i = true) : ∀ i < 1024, rowsAt D.EP D.RB D.LT D.KT i = true :=
  fun i hi => rowsAt_of_R hiv hK hi (h i hi)

end CertificateChecks.KernelCocode

end
