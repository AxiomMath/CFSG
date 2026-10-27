
module

public import Certificates.Kernel.Misc.E6StdBits
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.C2E6StdMatrixVec

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.Fischer CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel

attribute [local irreducible] mulB powB oneB rowStarts fullRow

@[expose] def blkF (c : K) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of ![![((F4.code c).val % 2 : ℕ), ((F4.code c).val / 2 : ℕ)],
    ![((F4.code c).val / 2 : ℕ), (((F4.code c).val % 2 + (F4.code c).val / 2 : ℕ) : ZMod 2)]]

@[expose] def blkHom : K →+* Matrix (Fin 2) (Fin 2) (ZMod 2) where
  toFun := blkF
  map_one' := by decide
  map_mul' := by
    intro x y
    revert x y
    decide
  map_zero' := by decide
  map_add' := by
    intro x y
    revert x y
    decide

@[expose] def unblk (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) : K :=
  ofBits (decide (m 0 0 = 1)) (decide (m 0 1 = 1))

theorem unblk_blkF (c : K) : unblk (blkF c) = c := by
  obtain ⟨n⟩ := c
  fin_cases n <;> rfl

theorem blkF_injective : Function.Injective blkF :=
  Function.LeftInverse.injective unblk_blkF

@[expose] def eqv : Fin 78 × Fin 2 ≃ Fin 156 := finProdFinEquiv

theorem eqv_val (k : Fin 78) (a : Fin 2) : (eqv (k, a) : ℕ) = a + 2 * k := rfl

@[expose] def blowM (M : Matrix (Fin 78) (Fin 78) K) : Matrix (Fin 156) (Fin 156) (ZMod 2) :=
  Matrix.of fun i j => blkF (M (eqv.symm i).1 (eqv.symm j).1) (eqv.symm i).2 (eqv.symm j).2

theorem blowM_apply (M : Matrix (Fin 78) (Fin 78) K) (k l : Fin 78) (a b : Fin 2) :
    blowM M (eqv (k, a)) (eqv (l, b)) = blkF (M k l) a b := by
  simp [blowM]

theorem blowM_mul (M N : Matrix (Fin 78) (Fin 78) K) : blowM (M * N) = blowM M * blowM N := by
  ext i j
  obtain ⟨⟨k, a⟩, rfl⟩ := eqv.surjective i
  obtain ⟨⟨l, b⟩, rfl⟩ := eqv.surjective j
  rw [blowM_apply, Matrix.mul_apply, Matrix.mul_apply]
  have e1 : blkF (∑ m, M k m * N m l) = ∑ m, blkF (M k m) * blkF (N m l) := by
    change blkHom (∑ m, M k m * N m l) = ∑ m, blkHom (M k m) * blkHom (N m l)
    rw [map_sum]
    simp only [map_mul]
  rw [e1, Matrix.sum_apply, ← eqv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [blowM_apply, blowM_apply]

theorem blowM_one : blowM 1 = 1 := by
  ext i j
  obtain ⟨⟨k, a⟩, rfl⟩ := eqv.surjective i
  obtain ⟨⟨l, b⟩, rfl⟩ := eqv.surjective j
  rw [blowM_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : k = l
  · subst h
    have e : blkF 1 = 1 := map_one blkHom
    simp only [↓reduceIte, e, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · have : eqv (k, a) ≠ eqv (k, b) := fun e => hab (Prod.ext_iff.1 (eqv.injective e)).2
      simp [hab, this]
  · have e : blkF 0 = 0 := map_zero blkHom
    have : eqv (k, a) ≠ eqv (l, b) := fun e => h (Prod.ext_iff.1 (eqv.injective e)).1
    simp [h, this, e]

theorem blowM_pow (M : Matrix (Fin 78) (Fin 78) K) (n : ℕ) : blowM (M ^ n) = blowM M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blowM_one]
  | succ n ih => rw [pow_succ, pow_succ, blowM_mul, ih]

theorem blowM_injective : Function.Injective blowM := by
  intro M M' h
  ext k l
  apply blkF_injective
  ext a b
  rw [← blowM_apply, ← blowM_apply, h]

@[expose] def Rep (N : ℕ) (M : Matrix (Fin 78) (Fin 78) K) : Prop :=
  N < 2 ^ 24336 ∧ decB N = blowM M

theorem rep_mulB {A B : ℕ} {M N : Matrix (Fin 78) (Fin 78) K} (hA : Rep A M) (hB : Rep B N) :
    Rep (mulB A B) (M * N) :=
  ⟨mulB_lt A B, by rw [decB_mulB, hA.2, hB.2, blowM_mul]⟩

theorem rep_oneB : Rep oneB 1 := ⟨oneB_lt, by rw [decB_oneB, blowM_one]⟩

theorem rep_powB {P : ℕ} {M : Matrix (Fin 78) (Fin 78) K} (hP : Rep P M) (n : ℕ) :
    Rep (powB P n) (M ^ n) :=
  ⟨powB_lt P n, by rw [decB_powB, hP.2, blowM_pow]⟩

theorem eq_iff_of_rep {N N' : ℕ} {M M' : Matrix (Fin 78) (Fin 78) K} (h : Rep N M)
    (h' : Rep N' M') : N = N' ↔ M = M' := by
  constructor
  · intro e
    apply blowM_injective
    rw [← h.2, ← h'.2, e]
  · intro e
    apply eq_of_decB_eq h.1 h'.1
    rw [h.2, h'.2, e]

theorem beq_iff_of_rep {N N' : ℕ} {M M' : Matrix (Fin 78) (Fin 78) K} (h : Rep N M)
    (h' : Rep N' M') : Nat.beq N N' = true ↔ M = M' := by
  rw [Nat.beq_eq, eq_iff_of_rep h h']

theorem rep_of_eq {N N' : ℕ} {M : Matrix (Fin 78) (Fin 78) K} (h : Rep N M)
    (e : Nat.beq N' N = true) : Rep N' M := by
  rw [Nat.beq_eq] at e
  rw [e]
  exact h

@[expose] def bb (x₀ x₁ : Bool) (a b : Fin 2) : Bool :=
  if a = 0 then (if b = 0 then x₀ else x₁) else (if b = 0 then x₁ else xor x₀ x₁)

theorem blkF_ofBits (x₀ x₁ : Bool) (a b : Fin 2) : blkF (ofBits x₀ x₁) a b = toZ (bb x₀ x₁ a b) := by
  cases x₀ <;> cases x₁ <;> fin_cases a <;> fin_cases b <;> decide

theorem decB_eqv (N : ℕ) (k l : Fin 78) (a b : Fin 2) :
    decB N (eqv (k, a)) (eqv (l, b)) = toZ (N.testBit (312 * k + 156 * a + 2 * l + b)) := by
  simp only [decB, Matrix.of_apply, eqv_val]
  congr 2
  ring

theorem rep_of_testBit {N : ℕ} {P : Native.Mat} (hN : N < 2 ^ 24336)
    (h : ∀ k l : Fin 78, ∀ a b : Fin 2, N.testBit (312 * k + 156 * a + 2 * l + b) =
      bb ((P.getD l (0, 0)).1.testBit k) ((P.getD l (0, 0)).2.testBit k) a b) :
    Rep N (toMat P) := by
  refine ⟨hN, ?_⟩
  ext i j
  obtain ⟨⟨k, a⟩, rfl⟩ := eqv.surjective i
  obtain ⟨⟨l, b⟩, rfl⟩ := eqv.surjective j
  rw [decB_eqv, blowM_apply, h]
  simp only [toMat, vecOf, Matrix.of_apply]
  rw [blkF_ofBits]

theorem letB_eq' (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem notB_eq' (a : Bool) : notB a = !a := by
  cases a <;> rfl

theorem ordP_of_ordB {P : ℕ} {X : Native.Mat} (h : Rep P (toMat X)) {p : ℕ}
    (ho : ordB P p = true) : Native.ordP X p = true := by
  have e : ordB P p = andB (Nat.beq (powB P p) oneB) (notB (Nat.beq P oneB)) := by
    unfold ordB
    exact letB_eq' _ _
  rw [e] at ho
  have h1 : Nat.beq (powB P p) oneB = true := by
    cases h' : Nat.beq (powB P p) oneB
    · rw [h'] at ho
      exact absurd ho Bool.false_ne_true
    · rfl
  have h2 : Nat.beq P oneB = false := by
    cases h' : Nat.beq P oneB
    · rfl
    · rw [h', h1] at ho
      exact absurd ho Bool.false_ne_true
  rw [beq_iff_of_rep (rep_powB h p) rep_oneB] at h1
  have h2' : toMat X ≠ 1 := by
    intro e
    have := (beq_iff_of_rep h rep_oneB).2 e
    rw [h2] at this
    exact absurd this Bool.false_ne_true
  unfold Native.ordP
  rw [Bool.and_eq_true]
  refine ⟨eqM_of_toMat_eq (by rw [toMat_pow, toMat_one, h1]), ?_⟩
  cases h3 : Native.eqM X Native.one
  · rfl
  · exact absurd ((toMat_eq_of_eqM h3).trans toMat_one) h2'

theorem eqM_iff_of_rep {N N' : ℕ} {X X' : Native.Mat} (h : Rep N (toMat X)) (h' : Rep N' (toMat X')) :
    Native.eqM X X' = Nat.beq N N' := by
  rw [Bool.eq_iff_iff, beq_iff_of_rep h h']
  exact ⟨toMat_eq_of_eqM, eqM_of_toMat_eq⟩

theorem rep_wordB {A B : ℕ} {X Y : Native.Mat} (hA : Rep A (toMat X)) (hB : Rep B (toMat Y))
    (w : List (ℕ × Bool)) : Rep (wordB A B w) (toMat (Native.wordMat X Y w)) := by
  have key : ∀ (acc : ℕ) (P : Native.Mat), Rep acc (toMat P) →
      Rep (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (Prod.rec (motive := fun _ => ℕ) (fun i s =>
          Bool.rec (motive := fun _ => ℕ)
            (Bool.rec (motive := fun _ => ℕ) (mulB acc (mulB B B)) (mulB acc B) s)
            (mulB acc A) (Nat.beq i 0)) l)) w acc)
        (toMat (w.foldl (fun acc l => Native.mul acc (Native.signedMat X Y l)) P)) := by
    induction w with
    | nil => intro acc P h; exact h
    | cons l w ih =>
      intro acc P h
      obtain ⟨i, s⟩ := l
      refine ih _ _ ?_
      rw [toMat_mul]
      unfold Native.signedMat
      rcases i with _ | i
      · exact rep_mulB h hA
      · have hb : Nat.beq (i + 1) 0 = false := rfl
        simp only [hb, Nat.add_one_ne_zero, ↓reduceIte]
        cases s
        · simp only [Bool.false_eq_true, ↓reduceIte, toMat_mul]
          exact rep_mulB h (rep_mulB hB hB)
        · exact rep_mulB h hB
  have e : wordB A B w = List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (Prod.rec (motive := fun _ => ℕ) (fun i s =>
          Bool.rec (motive := fun _ => ℕ)
            (Bool.rec (motive := fun _ => ℕ) (mulB acc (mulB B B)) (mulB acc B) s)
            (mulB acc A) (Nat.beq i 0)) l)) w oneB := rfl
  rw [e, Native.wordMat]
  exact key _ _ (toMat_one ▸ rep_oneB)

end CFSG.KC.Misc.E6Std

end
