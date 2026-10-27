module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TCheckInputs

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4070

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem p2 : (∀ i : Fin 5, bE i * bE i = 1) ∧ (∀ i j : Fin 5, bE i * bE j = bE j * bE i) ∧
    (∀ i : Fin 5, cE * bE i * cE⁻¹ = bE (i + 1)) ∧ (∀ i : Fin 5, dE * bE i * dE⁻¹ = bE (2 * i)) ∧
    cE ^ 5 = 1 ∧ cE ≠ 1 ∧ dE ^ 4 = 1 ∧ dE * cE * dE⁻¹ = cE ^ 2 ∧ cE * tE * cE⁻¹ = tE ∧
    dE * tE * dE⁻¹ = tE := by decide +kernel
theorem pB : ∀ i : Fin 5, bE i ∈ a2e5 := by decide +kernel
theorem p4 : ∀ x ∈ a2e5, x * x = 1 := by decide +kernel
theorem p6 : (tE * (yT * tE * yT⁻¹)) ^ 11 = 1 ∧ tE * (yT * tE * yT⁻¹) ≠ 1 ∧
    (bE 0 * (y0 * bE 0 * y0⁻¹)) ^ 11 = 1 ∧ bE 0 * (y0 * bE 0 * y0⁻¹) ≠ 1 := by decide +kernel
theorem p7 : ((x2M : NativeSporadic.M22) : Equiv.Perm (Fin 22)) =
      ((bE 0 * bE 1 : ↥m22A) : Equiv.Perm (Fin 22)) ∧
    ((x4M : NativeSporadic.M22) : Equiv.Perm (Fin 22)) =
      ((bE 0 * bE 1 * bE 2 * bE 3 : ↥m22A) : Equiv.Perm (Fin 22)) ∧
    bE 0 * bE 1 ≠ 1 ∧ bE 0 * bE 1 * bE 2 * bE 3 ≠ 1 := by decide +kernel
theorem p8 : (m22G2.all fun e => m22FG.any fun f => f.1 == e.1 && f.2.1 == e.2.1) = true := by
  decide +kernel

end CFSG.KD.LQT.C4070

end
