module

public import Certificates.Data.M23Norm3
public import CFSG.Quasithin.Background.B3Sign
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B3Basic

public section

namespace CertificateChecks.KernelM23Norm3

open Equiv CFSG.M23Norm3 CFSG.M23Heptad CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.Quasithin.B3

open scoped CFSG.Decide.Bounded in
theorem k4_vals : ∀ a0 : Fin 7, a0.val < 4 → ∀ a1 : Fin 7, a1.val < 4 → a1 ≠ a0 →
    ∀ a2 : Fin 7, a2.val < 4 → a2 ≠ a0 → a2 ≠ a1 →
    ∀ a3 : Fin 7, a3.val < 4 → a3 ≠ a0 → a3 ≠ a1 → a3 ≠ a2 →
    invCount (List.ofFn fun i => (![a0, a1, a2, a3, 4, 5, 6] i).val) % 2 = 0 →
    (∀ i : Fin 7, ![a0, a1, a2, a3, 4, 5, 6] (![a0, a1, a2, a3, 4, 5, 6]
      (![a0, a1, a2, a3, 4, 5, 6] (![a0, a1, a2, a3, 4, 5, 6] i))) = i) →
    ∃ τ ∈ k4List, ∀ i : Fin 7, ![a0, a1, a2, a3, 4, 5, 6] i = τ i := by
  decide +kernel

theorem cent_vals : ∀ a b : Fin 7,
    (∀ i j : Fin 7, ![0, a, c33 a, c33 (c33 a), b, c33 b, c33 (c33 b)] i =
      ![0, a, c33 a, c33 (c33 a), b, c33 b, c33 (c33 b)] j → i = j) →
    invCount (List.ofFn fun i => (![0, a, c33 a, c33 (c33 a), b, c33 b, c33 (c33 b)] i).val) %
      2 = 0 →
    ∃ x y : Fin 3, ∀ i : Fin 7, ![0, a, c33 a, c33 (c33 a), b, c33 b, c33 (c33 b)] i =
      (c33 ^ (x : ℕ) * c123 ^ (y : ℕ)) i := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem coset_check : ∀ i : Fin 16, ∀ a b : Fin 3,
    M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * yBar =
      yBar * (M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)) →
    M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * uBar =
      uBar * (M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)) →
    b = 0 ∧ M23Insp.es.getD i 1 * yBar = yBar * M23Insp.es.getD i 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem yBar_check :
    (∀ i : Fin 7, ((yBar : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
        ιbar (c33 i)) ∧
      (∀ i : Fin 7, ((y1Bar : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
        ιbar (c123 i)) ∧
      yBar ^ 3 = 1 ∧ yBar ≠ 1 ∧ y1Bar ^ 3 = 1 ∧ uBar * yBar = yBar * uBar ∧ uBar ≠ 1 ∧
      rBar * uBar = uBar * rBar ∧ rBar * yBar * rBar⁻¹ = yBar⁻¹ ∧
      (M23Insp.es.filter (fun e => e * yBar = yBar * e)).length = 4 := by
  decide +kernel

open scoped CFSG.Decide.Bounded

theorem perm7_mul : ∀ x ∈ k4List, ∀ y ∈ k4List, x * y ∈ k4List := by decide +kernel
theorem perm7_inv : ∀ x ∈ k4List, x⁻¹ ∈ k4List := by decide +kernel
theorem perm7_nodup : k4List.Nodup := by decide +kernel
theorem perm7_c123 : ∀ x ∈ k4List, c123 * x * c123⁻¹ ∈ k4List := by decide +kernel
theorem perm7_c456 : ∀ x ∈ k4List, c456 * x * c456⁻¹ ∈ k4List := by decide +kernel
theorem perm7_s1245 : ∀ x ∈ k4List, s1245 * x * s1245⁻¹ ∈ k4List := by decide +kernel
theorem perm7_comm : c123 * c456 = c456 * c123 := by decide +kernel
theorem perm7_c123_pow : c123 ^ 3 = 1 := by decide +kernel
theorem perm7_c456_pow : c456 ^ 3 = 1 := by decide +kernel
theorem perm7_sign_c123 : Perm.sign c123 = 1 := by decide +kernel
theorem perm7_sign_c456 : Perm.sign c456 = 1 := by decide +kernel
theorem perm7_sign_s1245 : Perm.sign s1245 = 1 := by decide +kernel
theorem perm7_s_c123 : s1245 * c123 * s1245⁻¹ = c123⁻¹ := by decide +kernel
theorem perm7_s_c456 : s1245 * c456 * s1245⁻¹ = c456⁻¹ := by decide +kernel
theorem perm7_e9 : e9List.Nodup := by decide +kernel

end CertificateChecks.KernelM23Norm3

end
