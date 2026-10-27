module

public import CFSG.Certificates.Kernel.Multipliers.MonoSound
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Rels
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Data.M12
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Data.M3
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Checks.M12
public import CFSG.Certificates.Kernel.Bounds.U43Alt.Checks.M3
public import CFSG.LieType.Multipliers.U43Kernel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.Open.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
public import Mathlib.Tactic.Ring

public section

namespace CertificateChecks.KernelU43

open CFSG.KC CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43 CFSG.CosetTable
  CFSG.Certificates.CosetEnumeration

theorem relCodes_eq : codes rels = CFSG.KC.U43Alt.relCodes := by decide

theorem coverCodes_eq :
    codes ((List.finRange 2).map fun i => (i, false) :: commWords (coverPairs i)) =
      CFSG.KC.U43Alt.coverCodes := by decide

theorem points_of_slices {p : ℕ → Bool} (h0 : Mono.allR 0 60 p = true)
    (h1 : Mono.allR 60 60 p = true) (h2 : Mono.allR 120 60 p = true)
    (h3 : Mono.allR 180 60 p = true) (h4 : Mono.allR 240 60 p = true)
    (h5 : Mono.allR 300 60 p = true) (h6 : Mono.allR 360 60 p = true)
    (h7 : Mono.allR 420 60 p = true) (h8 : Mono.allR 480 60 p = true) :
    ∀ x < 540, p x = true := by
  intro x hx
  have s := fun {lo : ℕ} (h : Mono.allR lo 60 p = true) (a : lo ≤ x) (b : x < lo + 60) =>
    CFSG.Certificates.Mono.allR_spec h x a b
  rcases Nat.lt_or_ge x 60 with c0 | c0
  · exact s h0 (Nat.zero_le _) c0
  rcases Nat.lt_or_ge x 120 with c1 | c1
  · exact s h1 c0 c1
  rcases Nat.lt_or_ge x 180 with c2 | c2
  · exact s h2 c1 c2
  rcases Nat.lt_or_ge x 240 with c3 | c3
  · exact s h3 c2 c3
  rcases Nat.lt_or_ge x 300 with c4 | c4
  · exact s h4 c3 c4
  rcases Nat.lt_or_ge x 360 with c5 | c5
  · exact s h5 c4 c5
  rcases Nat.lt_or_ge x 420 with c6 | c6
  · exact s h6 c5 c6
  rcases Nat.lt_or_ge x 480 with c7 | c7
  · exact s h7 c6 c7
  · exact s h8 c7 (by omega)

theorem points12 : ∀ x < 540, Mono.pointOK CFSG.KD.U43M12.Tab 2 540 12 CFSG.KD.U43M12.Cst
    CFSG.KC.U43Alt.relCodes CFSG.KC.U43Alt.coverCodes x = true :=
  points_of_slices CFSG.KD.U43M12.sP0 CFSG.KD.U43M12.sP1 CFSG.KD.U43M12.sP2 CFSG.KD.U43M12.sP3
    CFSG.KD.U43M12.sP4 CFSG.KD.U43M12.sP5 CFSG.KD.U43M12.sP6 CFSG.KD.U43M12.sP7 CFSG.KD.U43M12.sP8

theorem points3 : ∀ x < 540, Mono.pointOK CFSG.KD.U43M3.Tab 2 540 3 CFSG.KD.U43M3.Cst
    CFSG.KC.U43Alt.relCodes CFSG.KC.U43Alt.coverCodes x = true :=
  points_of_slices CFSG.KD.U43M3.sP0 CFSG.KD.U43M3.sP1 CFSG.KD.U43M3.sP2 CFSG.KD.U43M3.sP3
    CFSG.KD.U43M3.sP4 CFSG.KD.U43M3.sP5 CFSG.KD.U43M3.sP6 CFSG.KD.U43M3.sP7 CFSG.KD.U43M3.sP8

theorem zk_eq (k : ℕ) (hk : k < rels.length) :
    zk k = PresentedGroup.mk _ (FreeGroup.mk rels[k]) := by
  rw [zk, List.getD_eq_getElem _ _ hk]

theorem kernel_model : ∃ (E : Type) (_ : Group E) (ψ : PG 2 coverWs →* E)
    (τ : Multiplicative (ZMod 12 × ZMod 3) →* E), Function.Injective τ ∧
      ψ (zk 5) = τ (Multiplicative.ofAdd (4, 0)) ∧ ψ (zk 6) = τ (Multiplicative.ofAdd (9, 1)) := by
  obtain ⟨E₁, _, ψ₁, τ₁, hτ₁, h₁⟩ := CFSG.Certificates.Mono.mono_sound (N := 540) rels
    (fun i => commWords (coverPairs i)) relCodes_eq coverCodes_eq CFSG.KD.U43M12.sQ points12
  obtain ⟨E₂, _, ψ₂, τ₂, hτ₂, h₂⟩ := CFSG.Certificates.Mono.mono_sound (N := 540) rels
    (fun i => commWords (coverPairs i)) relCodes_eq coverCodes_eq CFSG.KD.U43M3.sQ points3
  let f₁ : Multiplicative (ZMod 12 × ZMod 3) →* Multiplicative (ZMod 12) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)
  let f₂ : Multiplicative (ZMod 12 × ZMod 3) →* Multiplicative (ZMod 3) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.snd _ _)
  refine ⟨E₁ × E₂, inferInstance, ψ₁.prod ψ₂, (τ₁.comp f₁).prod (τ₂.comp f₂), ?_, ?_, ?_⟩
  · intro x y hxy
    have e1 := hτ₁ (congrArg Prod.fst hxy)
    have e2 := hτ₂ (congrArg Prod.snd hxy)
    exact Multiplicative.toAdd.injective (Prod.ext (Multiplicative.ofAdd.symm.injective e1)
      (Multiplicative.ofAdd.symm.injective e2))
  · rw [zk_eq 5 (by decide), MonoidHom.prod_apply, h₁ 5 (by decide), h₂ 5 (by decide)]
    rfl
  · rw [zk_eq 6 (by decide), MonoidHom.prod_apply, h₁ 6 (by decide), h₂ 6 (by decide)]
    rfl

end CertificateChecks.KernelU43

end
