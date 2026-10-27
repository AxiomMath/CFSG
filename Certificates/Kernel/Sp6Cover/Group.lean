module

public import Mathlib.GroupTheory.Sylow

public section

namespace CertificateChecks.KernelSp6Cover

variable {G : Type*} [Group G]

theorem pow_mod_three {a : G} (ha : a ^ 3 = 1) (n : ℕ) : a ^ n = a ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ha, one_pow, one_mul]

theorem mul_form {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (i j k l : ℕ) :
    a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ ((i + k) % 3) * b ^ ((j + l) % 3) := by
  have hc : Commute (b ^ j) (a ^ k) := (Commute.symm hab).pow_pow j k
  calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by
        simp only [mul_assoc]
    _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hc.eq]
    _ = a ^ (i + k) * b ^ (j + l) := by simp only [pow_add, mul_assoc]
    _ = a ^ ((i + k) % 3) * b ^ ((j + l) % 3) := by
        rw [← pow_mod_three ha, ← pow_mod_three hb]

theorem closure_pair_form {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set G), ∃ i < 3, ∃ j < 3, x = a ^ i * b ^ j := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, by norm_num, 0, by norm_num, by simp⟩
    · exact ⟨0, by norm_num, 1, by norm_num, by simp⟩
  | one => exact ⟨0, by norm_num, 0, by norm_num, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, -, j, -, rfl⟩ := hx
    obtain ⟨k, -, l, -, rfl⟩ := hy
    exact ⟨_, Nat.mod_lt _ (by norm_num), _, Nat.mod_lt _ (by norm_num), mul_form ha hb hab i j k l⟩
  | inv x _ hx =>
    obtain ⟨i, -, j, -, rfl⟩ := hx
    refine ⟨(i + i) % 3, Nat.mod_lt _ (by norm_num), (j + j) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← mul_form ha hb hab]
    have hc : Commute (a ^ i) (b ^ j) := (Commute.pow_pow hab i j)
    have h3 : (a ^ i * b ^ j) ^ 3 = 1 := by
      rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul, ha, hb,
        one_pow, one_pow, one_mul]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← h3, pow_three]

theorem card_closure_pair {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a)
    (hne : ∀ i < 3, ∀ j < 3, a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 9 := by
  set H := Subgroup.closure ({a, b} : Set G) with hH
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  let f : Fin 3 × Fin 3 → H := fun q =>
    ⟨a ^ q.1.val * b ^ q.2.val, H.mul_mem (H.pow_mem haH _) (H.pow_mem hbH _)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ h
      have h' : a ^ i.val * b ^ j.val = a ^ k.val * b ^ l.val := congrArg Subtype.val h
      have e1 := mul_form ha hb hab i.val j.val (3 - k.val) (3 - l.val)
      have e2 := mul_form ha hb hab k.val l.val (3 - k.val) (3 - l.val)
      have hk := k.isLt
      have hl := l.isLt
      have hi := i.isLt
      have hj := j.isLt
      have z1 : (k.val + (3 - k.val)) % 3 = 0 := by omega
      have z2 : (l.val + (3 - l.val)) % 3 = 0 := by omega
      rw [z1, z2, pow_zero, pow_zero, one_mul] at e2
      rw [h', e2] at e1
      obtain ⟨h1, h2⟩ := hne _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) e1.symm
      exact Prod.ext (Fin.ext (by dsimp only; omega)) (Fin.ext (by dsimp only; omega))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, j, hj, rfl⟩ := closure_pair_form ha hb hab x hx
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

theorem factorization_4608_three : (4608 : ℕ).factorization 3 = 2 := by
  rw [show (4608 : ℕ) = 3 ^ 2 * 512 by norm_num, Nat.factorization_mul (by positivity) (by norm_num),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (p := 3) (by norm_num : ¬ 3 ∣ 512)]

noncomputable def sylowOf [Finite G] (hG : Nat.card G = 4608) {P : Subgroup G}
    (hP : Nat.card P = 9) : @Sylow 3 G _ :=
  @Sylow.ofCard G _ _ 3 ⟨Nat.prime_three⟩ P (by rw [hP, hG, factorization_4608_three]; norm_num)

theorem isPGroup_of_dvd_nine {H : Subgroup G} (h : Nat.card H ∣ 3 ^ 2) : IsPGroup 3 H := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.of_card hk

theorem odd_normal_eq_bot_of_disj [Finite G] (hG : Nat.card G = 4608) {P : Subgroup G}
    (hP : Nat.card P = 9) {c : G} (hdisj : ∀ x ∈ P, c * x * c⁻¹ ∈ P → x = 1)
    (M : Subgroup G) (hMn : ∀ g : G, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hM : Odd (Nat.card M)) :
    M = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : M.Normal := ⟨fun m hm g => hMn g m hm⟩
  have hdvd : Nat.card M ∣ 2 ^ 9 * 3 ^ 2 := by
    have := Subgroup.card_subgroup_dvd_card M
    rwa [hG] at this
  have hcop : Nat.Coprime (Nat.card M) (2 ^ 9) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hM)
  have hM3 : IsPGroup 3 M := isPGroup_of_dvd_nine (hcop.dvd_of_dvd_mul_left hdvd)
  have hMS : M ≤ (sylowOf hG hP : Subgroup G) := hM3.le_sylow_of_normal (sylowOf hG hP)
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  have h1 : c⁻¹ * m * c ∈ M := by
    have := hMn c⁻¹ m hm
    rwa [inv_inv] at this
  have e : c * (c⁻¹ * m * c) * c⁻¹ = m := by group
  have hx := hdisj _ (hMS h1) (by rw [e]; exact hMS hm)
  calc m = c * (c⁻¹ * m * c) * c⁻¹ := e.symm
    _ = 1 := by rw [hx]; group

theorem centralizes_or_of_sylow [Finite G] (hG : Nat.card G = 4608) {P : Subgroup G}
    (hP : Nat.card P = 9) (R : Subgroup G) (hR : ∀ g : G, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hgood : ∀ p ∈ P, (∀ r ∈ R, p * r = r * p) ∨ ∃ y, (∀ r ∈ R, y * r = r * y) ∧ p * y ≠ y * p)
    {x : G} (hx : x ^ 9 = 1) :
    (∀ r ∈ R, x * r = r * x) ∨ ∃ y, (∀ r ∈ R, y * r = r * y) ∧ x * y ≠ y * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine isPGroup_of_dvd_nine ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hx)
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (sylowOf hG hP) Q
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨p, hpP, hpx⟩ := hxQ
  rw [MulAut.smul_def, MulAut.conj_apply] at hpx
  subst hpx
  have hR' : ∀ r ∈ R, g⁻¹ * r * g ∈ R := fun r hr => by
    have := hR g⁻¹ r hr
    rwa [inv_inv] at this
  rcases hgood p hpP with hc | ⟨y, hy, hne⟩
  · left
    intro r hr
    have := hc _ (hR' r hr)
    calc g * p * g⁻¹ * r = g * (p * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * p) * g⁻¹ := by rw [this]
      _ = r * (g * p * g⁻¹) := by group
  · right
    refine ⟨g * y * g⁻¹, fun r hr => ?_, fun h => hne ?_⟩
    · have := hy _ (hR' r hr)
      calc g * y * g⁻¹ * r = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by rw [this]
        _ = r * (g * y * g⁻¹) := by group
    · calc p * y = g⁻¹ * (g * p * g⁻¹ * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * y * g⁻¹ * (g * p * g⁻¹)) * g := by rw [h]
        _ = y * p := by group

theorem conj_mem_closure {g : G} {t : Set G} (h : ∀ r ∈ t, g * r * g⁻¹ ∈ Subgroup.closure t) :
    ∀ r ∈ Subgroup.closure t, g * r * g⁻¹ ∈ Subgroup.closure t := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem conj_mem_of_closure [Finite G] {s : Set G} {R : Subgroup G}
    (hs : ∀ g ∈ s, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∀ c ∈ Subgroup.closure s, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
  let N : Submonoid G :=
    { carrier := {c | ∀ r ∈ R, c * r * c⁻¹ ∈ R}
      mul_mem' := fun {x y} hx hy r hr => by
        have e : x * y * r * (x * y)⁻¹ = x * (y * r * y⁻¹) * x⁻¹ := by group
        rw [e]
        exact hx _ (hy r hr)
      one_mem' := fun r hr => by simpa using hr }
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => intro r hr; simpa using hr
  | mul x y _ _ hx hy =>
    exact N.mul_mem (show x ∈ N from hx) (show y ∈ N from hy)
  | inv x _ hx =>
    have e : x ^ (orderOf x - 1) = x⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul (orderOf_pos x).ne', pow_orderOf_eq_one])
    rw [← e]
    exact N.pow_mem (show x ∈ N from hx) _

end CertificateChecks.KernelSp6Cover
