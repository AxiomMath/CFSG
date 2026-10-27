module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchExt
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillSpec
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelO8.FHom

open CFSG.EvenSmallLie.OmegaEight.SpBranch

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul) {gens : List ℕ}
include Φ

theorem mul_assoc_code {a b c : ℕ} (ha : a < N) (hb : b < N) (hc : c < N) :
    mul (mul a b) c = mul a (mul b c) := by
  rw [← Φ.f_g ha, ← Φ.f_g hb, ← Φ.f_g hc, ← Φ.map_mul, ← Φ.map_mul, ← Φ.map_mul, ← Φ.map_mul,
    mul_assoc]

theorem mul_lt_code {a b : ℕ} (ha : a < N) (hb : b < N) : mul a b < N := by
  rw [← Φ.f_g ha, ← Φ.f_g hb, ← Φ.map_mul]
  exact Φ.lt _

theorem mul_of_gens (h0 : mul 0 0 = 0) (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N)
    {F : ℕ → ℕ} (hlt : ∀ a < N, F a < N) (hF0 : F 0 = 0)
    (hstep : ∀ a < N, ∀ g ∈ gens, F (mul a g) = mul (F a) (F g)) {a c : ℕ} (ha : a < N)
    (hc : c < N) : F (mul a c) = mul (F a) (F c) := by
  have hr0 : ∀ x < N, mul x 0 = x := fun x hx => by
    rw [← Φ.f_g hx, ← Φ.f_one h0, ← Φ.map_mul, mul_one]
  induction hG c hc with
  | zero => rw [hr0 a ha, hF0, hr0 _ (hlt a ha)]
  | @step c g hr hg ih =>
    have hcl := reach_lt Φ hgens hr
    have hgl := hgens g hg
    rw [← mul_assoc_code Φ ha hcl hgl, hstep _ (mul_lt_code Φ ha hcl) g hg, ih hcl,
      mul_assoc_code Φ (hlt a ha) (hlt c hcl) (hlt g hgl), ← hstep c hcl g hg]

theorem mul_zero_code (h0 : mul 0 0 = 0) {a : ℕ} (ha : a < N) : mul a 0 = a := by
  rw [← Φ.f_g ha, ← Φ.f_one h0, ← Φ.map_mul, mul_one]

theorem zero_mul_code (h0 : mul 0 0 = 0) {a : ℕ} (ha : a < N) : mul 0 a = a := by
  rw [← Φ.f_g ha, ← Φ.f_one h0, ← Φ.map_mul, one_mul]

variable (h0 : mul 0 0 = 0) (hgens : ∀ g ∈ gens, g < N) (hG : Gen mul gens N)
include h0 hgens hG

theorem conj_of_gens {F : ℕ → ℕ} (hlt : ∀ a < N, F a < N) (hF0 : F 0 = 0)
    (hFmul : ∀ a < N, ∀ c < N, F (mul a c) = mul (F a) (F c)) {z : ℕ} (hz : z < N)
    (hgen : ∀ g ∈ gens, mul z g = mul (F (F g)) z) {y : ℕ} (hy : y < N) :
    mul z y = mul (F (F y)) z := by
  induction hG y hy with
  | zero => rw [hF0, hF0, mul_zero_code Φ h0 hz, zero_mul_code Φ h0 hz]
  | @step y g hr hg ih =>
    have hyl := reach_lt Φ hgens hr
    have hgl := hgens g hg
    have hFy := hlt _ (hlt _ hyl)
    have hFg := hlt _ (hlt _ hgl)
    rw [← mul_assoc_code Φ hz hyl hgl, ih hyl, mul_assoc_code Φ hFy hz hgl, hgen g hg,
      ← mul_assoc_code Φ hFy hFg hz, hFmul _ hyl _ hgl, hFmul _ (hlt _ hyl) _ (hlt _ hgl)]

omit h0 hgens hG in
theorem invOK_ext_of_conj {inv : ℕ → ℕ} (hinv : invOK mul inv N = true) {F : ℕ → ℕ}
    (hlt : ∀ a < N, F a < N) {z : ℕ} (hz : z < N)
    (hconj : ∀ y < N, mul z y = mul (F (F y)) z) :
    invOK (extMul N mul F z) (extInv N mul inv F z) (2 * N) = true := by
  unfold invOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  intro c hc
  by_cases hcN : c < N
  · obtain ⟨hil, hi⟩ := inv_spec hinv hcN
    refine ⟨by rw [extInv, ite_eq_left hcN]; omega, ?_⟩
    rw [extInv, ite_eq_left hcN, extMul, ite_eq_left hcN, ite_eq_left hil, hi]
  · have hk : c - N < N := by omega
    have hkz := mul_lt_code Φ hk hz
    obtain ⟨hil, hi⟩ := inv_spec hinv hkz
    have hnot : ¬ (F (inv (mul (c - N) z)) + N < N) := by omega
    refine ⟨by rw [extInv, ite_eq_right hcN]; have := hlt _ hil; omega, ?_⟩
    rw [extInv, ite_eq_right hcN, extMul, ite_eq_right hcN, ite_eq_right hnot, Nat.add_sub_cancel,
      mul_assoc_code Φ hk (hlt _ (hlt _ hil)) hz, ← hconj _ hil, ← mul_assoc_code Φ hk hz hil, hi]

end CertificateChecks.KernelO8.FHom

end
