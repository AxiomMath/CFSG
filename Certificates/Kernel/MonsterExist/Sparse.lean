module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CertificateChecks.MonsterExist.Sparse

abbrev Terms := List (ℕ × ℤ)

variable {M : Type*} [AddCommGroup M] [Module ℚ M] (b : ℕ → M)

@[expose] noncomputable def sumT (l : Terms) : M := (l.map fun t => (t.2 : ℚ) • b t.1).sum

@[simp] theorem sumT_nil : sumT b [] = 0 := rfl

@[simp] theorem sumT_cons (t : ℕ × ℤ) (l : Terms) :
    sumT b (t :: l) = (t.2 : ℚ) • b t.1 + sumT b l := rfl

theorem sumT_append (l l' : Terms) : sumT b (l ++ l') = sumT b l + sumT b l' := by
  simp [sumT]

@[expose] def stepT (col : ℕ → Terms) (l : Terms) : Terms :=
  l.flatMap fun t => (col t.1).map fun u => (u.1, t.2 * u.2)

theorem sumT_map_mul (c : ℤ) (l : Terms) :
    sumT b (l.map fun u => (u.1, c * u.2)) = (c : ℚ) • sumT b l := by
  induction l with
  | nil => simp
  | cons u l ih =>
    simp only [List.map_cons, sumT_cons, ih, smul_add, smul_smul]
    push_cast
    rfl

theorem map_sumT (f : M →ₗ[ℚ] M) (col : ℕ → Terms) (x : ℕ) (l : Terms)
    (h : ∀ t ∈ l, f (b t.1) = ((1 : ℚ) / 2 ^ x) • sumT b (col t.1)) :
    f (sumT b l) = ((1 : ℚ) / 2 ^ x) • sumT b (stepT col l) := by
  induction l with
  | nil => simp [stepT]
  | cons t l ih =>
    have h1 := h t List.mem_cons_self
    have h2 := ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [stepT, List.flatMap_cons] at h2 ⊢
    rw [sumT_append, sumT_cons, map_add, map_smul, h1, h2, sumT_map_mul, smul_add]
    rw [smul_comm]

inductive TT where
  | leaf : TT
  | node : TT → ℕ → ℤ → TT → TT

@[expose] def TT.ins (t : ℕ × ℤ) : TT → TT
  | .leaf => .node .leaf t.1 t.2 .leaf
  | .node l k c r =>
    if t.1 < k then .node (l.ins t) k c r
    else if t.1 = k then .node l k (t.2 + c) r
    else .node l k c (r.ins t)

@[expose] def TT.toL : TT → Terms
  | .leaf => []
  | .node l k c r => l.toL ++ (k, c) :: r.toL

theorem sumT_ins (t : ℕ × ℤ) (T : TT) :
    sumT b (T.ins t).toL = (t.2 : ℚ) • b t.1 + sumT b T.toL := by
  induction T with
  | leaf => simp [TT.ins, TT.toL]
  | node l k c r ihl ihr =>
    unfold TT.ins
    split_ifs with h1 h2
    · simp only [TT.toL, sumT_append, sumT_cons, ihl]
      abel
    · simp only [TT.toL, sumT_append, sumT_cons, h2]
      push_cast
      rw [add_smul]
      abel
    · simp only [TT.toL, sumT_append, sumT_cons, ihr]
      abel

@[expose] def normT (l : Terms) : Terms :=
  ((l.foldr (fun t T => T.ins t) TT.leaf).toL).filter fun t => t.2 != 0

theorem sumT_filter_ne (l : Terms) : sumT b (l.filter fun t => t.2 != 0) = sumT b l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h : t.2 = 0
    · simp [h, ih]
    · simp [h, ih]

theorem sumT_normT (l : Terms) : sumT b (normT l) = sumT b l := by
  unfold normT
  rw [sumT_filter_ne]
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.foldr_cons, sumT_ins, ih, sumT_cons]

@[expose] def negT (l : Terms) : Terms := l.map fun t => (t.1, -t.2)

theorem sumT_negT (l : Terms) : sumT b (negT l) = -sumT b l := by
  induction l with
  | nil => simp [negT]
  | cons t l ih =>
    simp only [negT, List.map_cons, sumT_cons] at ih ⊢
    rw [ih, neg_add]
    push_cast
    rw [neg_smul]

@[expose] def eqT : Terms → Terms → Bool
  | [], [] => true
  | t :: l, u :: l' => Nat.beq t.1 u.1 && t.2 == u.2 && eqT l l'
  | _, _ => false

theorem eq_of_eqT : ∀ {l l' : Terms}, eqT l l' = true → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | t :: l, u :: l', h => by
    simp only [eqT, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Prod.ext h1 h2, eq_of_eqT h3]

@[expose] def scaleT (f : ℕ) (l : Terms) : Terms := l.map fun t => (t.1, t.2 * 2 ^ f)

theorem sumT_scaleT (f : ℕ) (l : Terms) : sumT b (scaleT f l) = (2 : ℚ) ^ f • sumT b l := by
  induction l with
  | nil => simp [scaleT]
  | cons t l ih =>
    simp only [scaleT, List.map_cons, sumT_cons] at ih ⊢
    rw [ih, smul_add, smul_smul]
    push_cast
    rw [mul_comm]

@[expose] def eqST (e : ℕ) (l : Terms) (e' : ℕ) (l' : Terms) : Bool :=
  eqT (normT (scaleT (max e e' - e) l)) (normT (scaleT (max e e' - e') l'))

theorem smul_sumT_eq_of_eqT {e e' : ℕ} {l l' : Terms} (h : eqST e l e' l' = true) :
    ((1 : ℚ) / 2 ^ e) • sumT b l = ((1 : ℚ) / 2 ^ e') • sumT b l' := by
  have h1 := congrArg (sumT b) (eq_of_eqT h)
  rw [sumT_normT, sumT_normT, sumT_scaleT, sumT_scaleT] at h1
  have hm : ∀ x : ℕ, x ≤ max e e' → ((1 : ℚ) / 2 ^ x) = (1 / 2 ^ max e e') * 2 ^ (max e e' - x) :=
    fun x hx => by
      have hp : (2 : ℚ) ^ max e e' = 2 ^ x * 2 ^ (max e e' - x) := by
        rw [← pow_add, Nat.add_sub_cancel' hx]
      rw [hp]
      field_simp
  rw [hm e (le_max_left _ _), hm e' (le_max_right _ _), mul_smul, mul_smul]
  exact congrArg (((1 : ℚ) / 2 ^ max e e') • ·) h1

@[expose] def runT {G : Type} (ok : G → ℕ → Bool) (col : G → ℕ → Terms) (ex : G → ℕ) :
    List G → Bool × ℕ × Terms → Bool × ℕ × Terms
  | [], s => s
  | g :: w, (f, e, l) => runT ok col ex w (f && l.all (fun t => ok g t.1), e + ex g, stepT (col g) l)

theorem runT_flag {G : Type} (ok : G → ℕ → Bool) (col : G → ℕ → Terms) (ex : G → ℕ) :
    ∀ (w : List G) (e : ℕ) (l : Terms), (runT ok col ex w (false, e, l)).1 = false
  | [], _, _ => rfl
  | _ :: w, _, _ => runT_flag ok col ex w _ _

theorem runT_sound {G : Type} (sem : G → M →ₗ[ℚ] M) (ok : G → ℕ → Bool) (col : G → ℕ → Terms)
    (ex : G → ℕ) :
    ∀ (w : List G), (∀ g ∈ w, ∀ k, ok g k = true →
      sem g (b k) = ((1 : ℚ) / 2 ^ ex g) • sumT b (col g k)) →
    ∀ (e : ℕ) (l : Terms), (runT ok col ex w (true, e, l)).1 = true →
      w.foldl (fun x g => sem g x) (((1 : ℚ) / 2 ^ e) • sumT b l) =
        ((1 : ℚ) / 2 ^ (runT ok col ex w (true, e, l)).2.1) •
          sumT b (runT ok col ex w (true, e, l)).2.2
  | [], _, e, l, _ => rfl
  | g :: w, hw, e, l, hf => by
    simp only [runT] at hf ⊢
    by_cases ha : (l.all fun t => ok g t.1) = true
    · rw [Bool.true_and, ha] at hf ⊢
      rw [List.foldl_cons, ← runT_sound sem ok col ex w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
        _ _ hf]
      congr 1
      rw [map_smul, map_sumT b (sem g) (col g) (ex g) l fun t ht =>
        hw g List.mem_cons_self t.1 (List.all_eq_true.1 ha t ht), smul_smul, pow_add]
      congr 1
      field_simp
    · rw [Bool.not_eq_true] at ha
      rw [Bool.true_and, ha, runT_flag] at hf
      exact absurd hf Bool.false_ne_true

end CertificateChecks.MonsterExist.Sparse
