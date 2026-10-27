module

public import CFSG.Certificates.Kernel.Multipliers.LabZSound
public import Mathlib.Algebra.Group.Commute.Basic

public section

namespace CertificateChecks.KernelMult

open CFSG.Certificates.LabZ

variable {G : Type*} [Group G] (g : ℕ → G)

theorem zprod_succ (D : ℕ) (v : ℕ → ℤ) : zprod g (D + 1) v = zprod g D v * g D ^ v D := by
  unfold zprod
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem zprod_congr {D : ℕ} {a b : ℕ → ℤ} (h : ∀ d < D, a d = b d) : zprod g D a = zprod g D b := by
  induction D with
  | zero => rfl
  | succ D ih =>
    rw [zprod_succ, zprod_succ, ih fun d hd => h d (by omega), h D (by omega)]

theorem zprod_zero_vec (D : ℕ) : zprod g D 0 = 1 := by
  induction D with
  | zero => rfl
  | succ D ih => rw [zprod_succ, ih, Pi.zero_apply, zpow_zero, mul_one]

variable {g}

theorem commute_zprod (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (v : ℕ → ℤ) (e : ℕ) (k : ℤ) :
    Commute (zprod g D v) (g e ^ k) := by
  induction D with
  | zero => exact Commute.one_left _
  | succ D ih =>
    rw [zprod_succ]
    exact Commute.mul_left ih (Commute.zpow_zpow (hc D e) _ _)

theorem zprod_add (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (a b : ℕ → ℤ) :
    zprod g D (a + b) = zprod g D a * zprod g D b := by
  induction D with
  | zero => rw [show zprod g 0 (a + b) = 1 from rfl, show zprod g 0 a = 1 from rfl,
      show zprod g 0 b = 1 from rfl, one_mul]
  | succ D ih =>
    rw [zprod_succ, zprod_succ, zprod_succ, ih, Pi.add_apply, zpow_add]
    have h1 : zprod g D b * g D ^ a D = g D ^ a D * zprod g D b := (commute_zprod hc D b D (a D)).eq
    calc zprod g D a * zprod g D b * (g D ^ a D * g D ^ b D)
        = zprod g D a * (zprod g D b * g D ^ a D) * g D ^ b D := by simp only [mul_assoc]
      _ = zprod g D a * (g D ^ a D * zprod g D b) * g D ^ b D := by rw [h1]
      _ = zprod g D a * g D ^ a D * (zprod g D b * g D ^ b D) := by simp only [mul_assoc]

theorem zprod_neg (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (a : ℕ → ℤ) :
    zprod g D (-a) = (zprod g D a)⁻¹ := by
  have h := zprod_add hc D a (-a)
  rw [add_neg_cancel, zprod_zero_vec] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem zprod_sub (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (a b : ℕ → ℤ) :
    zprod g D (a - b) = zprod g D a * (zprod g D b)⁻¹ := by
  rw [sub_eq_add_neg, zprod_add hc, zprod_neg hc]

theorem zprod_zsmul (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (c : ℤ) (a : ℕ → ℤ) :
    zprod g D (c • a) = zprod g D a ^ c := by
  induction D with
  | zero => rw [show zprod g 0 (c • a) = 1 from rfl, show zprod g 0 a = 1 from rfl, one_zpow]
  | succ D ih =>
    rw [zprod_succ, zprod_succ, ih, Pi.smul_apply, smul_eq_mul, mul_comm c (a D), zpow_mul]
    exact (Commute.mul_zpow (commute_zprod hc D a D (a D)) c).symm

theorem zprod_combo (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) :
    ∀ (vs : List ((ℕ → ℤ) × ℤ)), (∀ p ∈ vs, zprod g D p.1 = 1) →
      zprod g D (vs.map fun p => p.2 • p.1).sum = 1
  | [], _ => by
    rw [List.map_nil, List.sum_nil]
    exact zprod_zero_vec g D
  | p :: vs, h => by
    rw [List.map_cons, List.sum_cons, zprod_add hc, zprod_zsmul hc, h p List.mem_cons_self,
      one_zpow, one_mul]
    exact zprod_combo hc D vs fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem zprod_eq_one {D : ℕ} {t : ℕ → ℤ} (h : ∀ d < D, g d ^ t d = 1) : zprod g D t = 1 := by
  induction D with
  | zero => rfl
  | succ D ih => rw [zprod_succ, ih fun d hd => h d (by omega), h D (by omega), mul_one]

theorem zprod_eq_single {D k : ℕ} (hk : k < D) {t : ℕ → ℤ} (h1 : t k = 1)
    (h : ∀ d < D, d ≠ k → g d ^ t d = 1) : zprod g D t = g k := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [zprod_succ]
    rcases Nat.lt_or_ge k D with hkD | hkD
    · rw [ih hkD fun d hd hdk => h d (by omega) hdk, h D (by omega) (by omega), mul_one]
    · have e : k = D := by omega
      subst e
      rw [zprod_eq_one fun d hd => h d (by omega) (by omega), one_mul, h1, zpow_one]

theorem zprod_eq_pow {D k : ℕ} (hk : k < D) {t : ℕ → ℤ}
    (h : ∀ d < D, d ≠ k → g d ^ t d = 1) : zprod g D t = g k ^ t k := by
  induction D with
  | zero => omega
  | succ D ih =>
    rw [zprod_succ]
    rcases Nat.lt_or_ge k D with hkD | hkD
    · rw [ih hkD fun d hd hdk => h d (by omega) hdk, h D (by omega) (by omega), mul_one]
    · have e : k = D := by omega
      subst e
      rw [zprod_eq_one fun d hd => h d (by omega) (by omega), one_mul]

theorem zprod_zip (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) :
    ∀ (cs : List ℤ) (ρs : List (ℕ → ℤ)), (∀ ρ ∈ ρs, zprod g D ρ = 1) →
      zprod g D (List.zipWith (fun c ρ => c • ρ) cs ρs).sum = 1
  | [], _, _ => by
    rw [List.zipWith_nil_left, List.sum_nil]
    exact zprod_zero_vec g D
  | _ :: _, [], _ => by
    rw [List.zipWith_nil_right, List.sum_nil]
    exact zprod_zero_vec g D
  | c :: cs, ρ :: ρs, h => by
    rw [List.zipWith_cons_cons, List.sum_cons, zprod_add hc, zprod_zsmul hc, h ρ List.mem_cons_self,
      one_zpow, one_mul]
    exact zprod_zip hc D cs ρs fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem zprod_target (hc : ∀ i j, Commute (g i) (g j)) (D : ℕ) (cs : List ℤ) (ρs : List (List ℤ))
    (hρ : ∀ ρ ∈ ρs, zprod g D (fun d => ρ.getD d 0) = 1) (t : List ℤ)
    (ht : ∀ d < D, (List.zipWith (fun c ρ => c • ρ) cs (ρs.map fun ρ d => ρ.getD d 0)).sum d =
      t.getD d 0) :
    zprod g D (fun d => t.getD d 0) = 1 := by
  rw [← zprod_congr g ht]
  refine zprod_zip hc D cs _ fun ρ hρ' => ?_
  obtain ⟨ρ₀, h₀, rfl⟩ := List.mem_map.1 hρ'
  exact hρ ρ₀ h₀

end CertificateChecks.KernelMult

end
