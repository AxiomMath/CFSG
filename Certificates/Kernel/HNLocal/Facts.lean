module

public import CFSG.Sporadic.HN.LocalK
import Certificates.Kernel.HNLocal.Fix
import Certificates.Kernel.HNLocal.Orbit
import Certificates.Kernel.HNLocal.Census
public import CFSG.Certificates.Kernel.HNLocalSound
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CertificateChecks.KernelHNLocal

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK

theorem facts6097 : wG 2 • rootV = rootV ∧ wG 3 • rootV = rootV ∧ Function.Injective hnW ∧
    (∀ k, wG 2 • hnW k = hnW (pi2 k)) ∧ (∀ k, wG 3 • hnW k = hnW (pi3 k)) ∧
    1140000 ≤ Nat.card (MulAction.orbit (J dHN) rootV) :=
  ⟨x2_root, x3_root, hnW_injective, x2_W, x3_W, card_orbit_ge⟩

theorem facts6098 : wG 12 ^ 2 = 1 ∧ wG 13 ^ 2 = 1 ∧ wG 12 ≠ 1 ∧ wG 13 ≠ 1 ∧
    (mat dHN (wG 12)).trace ≠ (mat dHN (wG 13)).trace ∧
    ∃ Q : Subgroup (J dHN), Nat.card Q = 2 ^ 14 ∧ ∀ g ∈ Q, g ^ 2 = 1 → g ≠ 1 →
      ∃ (i : Fin 2) (h : J dHN) (m : ℕ), m % 2 = 1 ∧ (g * (h * wG (12 + i.val) * h⁻¹)) ^ m = 1 :=
  ⟨t2_sq, t4_sq, t2_ne_one, t4_ne_one, trace_ne, QJ, card_QJ, census⟩

theorem facts6099 : wG 12 • rootV = rootV ∧ wG 13 • rootV = rootV ∧
    (∀ k, wG 12 • hnW k = hnW (pit2 k)) ∧ (∀ k, wG 13 • hnW k = hnW (pit4 k)) ∧ wG 14 = wG 2 ∧
    ∃ X : Fin 1140000 → Vec dHN, Function.Injective X ∧
      (∀ k, X k ∈ MulAction.orbit (J dHN) rootV) ∧
      Nat.card {k // wG 12 • X k = X k} = 8800 ∧ Nat.card {k // wG 13 • X k = X k} = 800 :=
  ⟨t2_root, t4_root, t2_W, t4_W, wG14, fun k => Xk k.val,
    fun i j e => Fin.ext (Xk_injective i.val i.2 j.val j.2 e), fun k => Xk_mem_orbit k.val k.2,
    card_fix_t2, card_fix_t4⟩

end CertificateChecks.KernelHNLocal

end
