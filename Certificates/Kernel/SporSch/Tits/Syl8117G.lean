module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CertificateChecks.KernelSporSch.Heis3

variable {M : Type*} [Group M]

structure Rel3 (x y z : M) (j : ℕ) : Prop where
  x3 : x ^ 3 = 1
  y3 : y ^ 3 = 1
  z3 : z ^ 3 = 1
  xy : x * y = y * x
  xz : x * z = z * x
  zy : z * y = x ^ j * (y * z)
  j12 : j = 1 ∨ j = 2
  x1 : x ≠ 1

@[expose] def f (x y z : M) (t : ℕ × ℕ × ℕ) : M := x ^ t.1 * y ^ t.2.1 * z ^ t.2.2

@[expose] def mulT (j : ℕ) (t s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  ((t.1 + s.1 + j * (t.2.2 * s.2.1)) % 3, (t.2.1 + s.2.1) % 3, (t.2.2 + s.2.2) % 3)

@[expose] def conjT (j : ℕ) (s t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := mulT j (mulT j s t) (mulT j s s)

@[expose] def Bd (t : ℕ × ℕ × ℕ) : Prop := t.1 < 3 ∧ t.2.1 < 3 ∧ t.2.2 < 3

theorem pow_mod3 {g : M} (h : g ^ 3 = 1) (n : ℕ) : g ^ n = g ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h, one_pow, one_mul]

variable {x y z : M} {j : ℕ}

theorem Rel3.cxy (R : Rel3 x y z j) (m n : ℕ) : x ^ m * y ^ n = y ^ n * x ^ m :=
  (Commute.pow_pow (R.xy : Commute x y) m n).eq

theorem Rel3.cxz (R : Rel3 x y z j) (m n : ℕ) : x ^ m * z ^ n = z ^ n * x ^ m :=
  (Commute.pow_pow (R.xz : Commute x z) m n).eq

theorem swap1 (R : Rel3 x y z j) : ∀ c : ℕ, z ^ c * y = x ^ (j * c) * (y * z ^ c)
  | 0 => by simp
  | c + 1 => by
    have hxz : x ^ j * z ^ c = z ^ c * x ^ j := R.cxz j c
    have e : j * (c + 1) = j + j * c := by ring
    calc z ^ (c + 1) * y = z ^ c * (z * y) := by rw [pow_succ, mul_assoc]
      _ = z ^ c * (x ^ j * (y * z)) := by rw [R.zy]
      _ = z ^ c * x ^ j * y * z := by simp only [mul_assoc]
      _ = x ^ j * (z ^ c * y) * z := by rw [← hxz]; simp only [mul_assoc]
      _ = x ^ j * (x ^ (j * c) * (y * z ^ c)) * z := by rw [swap1 R c]
      _ = x ^ (j * (c + 1)) * (y * z ^ (c + 1)) := by
        rw [e, pow_add, pow_succ]
        simp only [mul_assoc]

theorem swap (R : Rel3 x y z j) (c : ℕ) :
    ∀ b : ℕ, z ^ c * y ^ b = x ^ (j * (c * b)) * (y ^ b * z ^ c)
  | 0 => by simp
  | b + 1 => by
    have hxy : x ^ (j * c) * y ^ b = y ^ b * x ^ (j * c) := R.cxy (j * c) b
    have e : j * (c * (b + 1)) = j * (c * b) + j * c := by ring
    calc z ^ c * y ^ (b + 1) = z ^ c * y ^ b * y := by rw [pow_succ, mul_assoc]
      _ = x ^ (j * (c * b)) * (y ^ b * z ^ c) * y := by rw [swap R c b]
      _ = x ^ (j * (c * b)) * y ^ b * (z ^ c * y) := by simp only [mul_assoc]
      _ = x ^ (j * (c * b)) * y ^ b * (x ^ (j * c) * (y * z ^ c)) := by rw [swap1 R c]
      _ = x ^ (j * (c * b)) * (y ^ b * x ^ (j * c)) * y * z ^ c := by simp only [mul_assoc]
      _ = x ^ (j * (c * b)) * (x ^ (j * c) * y ^ b) * y * z ^ c := by rw [← hxy]
      _ = x ^ (j * (c * (b + 1))) * (y ^ (b + 1) * z ^ c) := by
        rw [e, pow_add, pow_succ]
        simp only [mul_assoc]

theorem f_mul (R : Rel3 x y z j) (t s : ℕ × ℕ × ℕ) : f x y z t * f x y z s = f x y z (mulT j t s) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := s
  have hxy := R.cxy
  have hxz := R.cxz
  change x ^ a * y ^ b * z ^ c * (x ^ a' * y ^ b' * z ^ c') =
    x ^ ((a + a' + j * (c * b')) % 3) * y ^ ((b + b') % 3) * z ^ ((c + c') % 3)
  rw [← pow_mod3 R.x3, ← pow_mod3 R.y3, ← pow_mod3 R.z3]
  calc x ^ a * y ^ b * z ^ c * (x ^ a' * y ^ b' * z ^ c')
      = x ^ a * y ^ b * (z ^ c * x ^ a') * y ^ b' * z ^ c' := by simp only [mul_assoc]
    _ = x ^ a * y ^ b * (x ^ a' * z ^ c) * y ^ b' * z ^ c' := by rw [← hxz a' c]
    _ = x ^ a * (y ^ b * x ^ a') * (z ^ c * y ^ b') * z ^ c' := by simp only [mul_assoc]
    _ = x ^ a * (x ^ a' * y ^ b) * (x ^ (j * (c * b')) * (y ^ b' * z ^ c)) * z ^ c' := by
      rw [← hxy a' b, swap R c b']
    _ = x ^ a * x ^ a' * (y ^ b * x ^ (j * (c * b'))) * y ^ b' * (z ^ c * z ^ c') := by
      simp only [mul_assoc]
    _ = x ^ a * x ^ a' * (x ^ (j * (c * b')) * y ^ b) * y ^ b' * (z ^ c * z ^ c') := by
      rw [← hxy (j * (c * b')) b]
    _ = x ^ (a + a' + j * (c * b')) * y ^ (b + b') * z ^ (c + c') := by
      simp only [pow_add, mul_assoc]

theorem f_zero : f x y z (0, 0, 0) = 1 := by simp [f]

theorem cubeB : (List.range 3).all (fun j => (List.range 3).all (fun a => (List.range 3).all
    (fun b => (List.range 3).all (fun c =>
      mulT j (a, b, c) (mulT j (a, b, c) (a, b, c)) == (0, 0, 0))))) = true := by
  decide +kernel

theorem cubeT : ∀ j < 3, ∀ a < 3, ∀ b < 3, ∀ c < 3,
    mulT j (a, b, c) (mulT j (a, b, c) (a, b, c)) = (0, 0, 0) := by
  have h := cubeB
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem invB : (List.range 3).all (fun j => (List.range 3).all (fun a => (List.range 3).all
    (fun b => (List.range 3).all (fun c => (List.range 3).all (fun a' => (List.range 3).all
      (fun b' => (List.range 3).all (fun c' =>
        !(mulT j (a, b, c) (mulT j (a', b', c') (a', b', c')) == (0, 0, 0)) ||
          (a, b, c) == (a', b', c')))))))) = true := by
  decide +kernel

theorem invT : ∀ j < 3, ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ a' < 3, ∀ b' < 3, ∀ c' < 3,
    mulT j (a, b, c) (mulT j (a', b', c') (a', b', c')) = (0, 0, 0) → (a, b, c) = (a', b', c') := by
  have h := invB
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq] at h
  intro j hj a ha b hb c hc a' ha' b' hb' c' hc' e
  exact (h j hj a ha b hb c hc a' ha' b' hb' c' hc').resolve_left (not_not.2 e)

theorem j_lt (R : Rel3 x y z j) : j < 3 := by rcases R.j12 with rfl | rfl <;> norm_num

theorem f_cube (R : Rel3 x y z j) {t : ℕ × ℕ × ℕ} (ht : Bd t) :
    f x y z t * (f x y z t * f x y z t) = 1 := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hb, hc⟩ := ht
  rw [f_mul R, f_mul R, cubeT j (j_lt R) a ha b hb c hc, f_zero]

theorem f_inv (R : Rel3 x y z j) {t : ℕ × ℕ × ℕ} (ht : Bd t) :
    (f x y z t)⁻¹ = f x y z (mulT j t t) := by
  rw [← f_mul R]
  exact inv_eq_of_mul_eq_one_right (f_cube R ht)

theorem bd_mulT (t s : ℕ × ℕ × ℕ) : Bd (mulT j t s) :=
  ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

theorem x_pow_inj (R : Rel3 x y z j) {m n : ℕ} (hm : m < 3) (hn : n < 3) (h : x ^ m = x ^ n) :
    m = n := by
  have h2 : x ^ 2 ≠ 1 := fun e => R.x1 (by
    have := R.x3
    rwa [pow_succ, e, one_mul] at this)
  have h12 : x ^ 1 ≠ x ^ 2 := fun e => R.x1 (by
    rw [pow_one, pow_two] at e
    exact (mul_eq_left.1 e.symm))
  interval_cases m <;> interval_cases n <;> simp_all [eq_comm]

theorem eq_zero_of_f (R : Rel3 x y z j) {t : ℕ × ℕ × ℕ} (ht : Bd t) (h : f x y z t = 1) :
    t = (0, 0, 0) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨ha, hb, hc⟩ : a < 3 ∧ b < 3 ∧ c < 3 := ht
  have k1 := f_mul R (a, b, c) (0, 1, 0)
  have k2 := f_mul R (0, 1, 0) (a, b, c)
  have k3 := f_mul R (a, b, c) (0, 0, 1)
  have k4 := f_mul R (0, 0, 1) (a, b, c)
  rw [h, one_mul] at k1 k3
  rw [h, mul_one] at k2 k4
  have e1 := k1.symm.trans k2
  have e2 := k3.symm.trans k4
  simp only [f, mulT, Nat.add_zero, Nat.zero_add, Nat.mul_one, Nat.one_mul, Nat.mul_zero,
    Nat.zero_mul, Nat.add_comm b 1, Nat.add_comm c 1] at e1 e2
  have c0 := x_pow_inj R (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (mul_right_cancel (mul_right_cancel e1))
  have b0 := x_pow_inj R (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (mul_right_cancel (mul_right_cancel e2))
  have hc0 : c = 0 := by rcases R.j12 with rfl | rfl <;> omega
  have hb0 : b = 0 := by rcases R.j12 with rfl | rfl <;> omega
  subst hc0 hb0
  have a0 : x ^ a = x ^ 0 := by simpa [f] using h
  have ha0 := x_pow_inj R ha (by norm_num) a0
  rw [ha0]

theorem f_inj (R : Rel3 x y z j) {t s : ℕ × ℕ × ℕ} (ht : Bd t) (hs : Bd s)
    (h : f x y z t = f x y z s) : t = s := by
  have e : f x y z (mulT j t (mulT j s s)) = 1 := by
    rw [← f_mul R, ← f_inv R hs, h, mul_inv_cancel]
  have e0 := eq_zero_of_f R (bd_mulT _ _) e
  obtain ⟨a, b, c⟩ := t
  obtain ⟨a', b', c'⟩ := s
  obtain ⟨ha, hb, hc⟩ := ht
  obtain ⟨ha', hb', hc'⟩ := hs
  exact invT j (j_lt R) a ha b hb c hc a' ha' b' hb' c' hc' e0

theorem f_conj (R : Rel3 x y z j) {s : ℕ × ℕ × ℕ} (hs : Bd s) (t : ℕ × ℕ × ℕ) :
    f x y z s * f x y z t * (f x y z s)⁻¹ = f x y z (conjT j s t) := by
  rw [f_inv R hs, f_mul R, f_mul R]
  rfl

theorem yz_ne (R : Rel3 x y z j) : y * z ≠ z * y := by
  intro h
  have e : x ^ j * (y * z) = 1 * (y * z) := by rw [← R.zy, one_mul, h]
  have := x_pow_inj R (j_lt R) (by norm_num : 0 < 3) (by rw [pow_zero]; exact mul_right_cancel e)
  rcases R.j12 with rfl | rfl <;> omega

end CertificateChecks.KernelSporSch.Heis3

end
