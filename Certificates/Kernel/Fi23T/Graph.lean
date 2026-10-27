module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Pointwise

namespace CertificateChecks.KernelFi23T

variable {P : Type*} [DecidableEq P]

structure TSys (A : Subgroup (Equiv.Perm P)) (τ : P → Equiv.Perm P) : Prop where
  mem : ∀ x, τ x ∈ A
  conj : ∀ g ∈ A, ∀ x, τ (g x) = g * τ x * g⁻¹
  sq : ∀ x, τ x * τ x = 1
  inj : Function.Injective τ

@[expose] def Adj (τ : P → Equiv.Perm P) (V W : Finset P) : Prop := ∃ h, h ∉ V ∧ W = τ h • V

@[expose] def Orb (τ : P → Equiv.Perm P) (X : Set P) (y : P) : Set P :=
  {x | ∃ g ∈ Subgroup.closure (τ '' X), g y = x}

theorem orb_self (τ : P → Equiv.Perm P) (X : Set P) (y : P) : y ∈ Orb τ X y :=
  ⟨1, one_mem _, rfl⟩

theorem orb_step {τ : P → Equiv.Perm P} {X : Set P} {y x s : P} (hx : x ∈ Orb τ X y)
    (hs : s ∈ X) : τ s x ∈ Orb τ X y := by
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨τ s * g, mul_mem (Subgroup.subset_closure ⟨s, hs, rfl⟩) hg, rfl⟩

theorem orb_mono {τ : P → Equiv.Perm P} {X Y : Set P} (h : X ⊆ Y) {y x : P}
    (hx : x ∈ Orb τ X y) : x ∈ Orb τ Y y := by
  obtain ⟨g, hg, rfl⟩ := hx
  exact ⟨g, Subgroup.closure_mono (Set.image_mono h) hg, rfl⟩

theorem path_closure {α G : Type*} [Group G] [MulAction G α] {Sg : Set G} {R : α → α → Prop}
    (hsym : ∀ a b, R a b → R b a) (hinv : ∀ g ∈ Subgroup.closure Sg, ∀ a b, R a b →
      R (g • a) (g • b)) {m₀ : α} (hgen : ∀ s ∈ Sg, s • m₀ = m₀ ∨ R m₀ (s • m₀)) :
    ∀ g ∈ Subgroup.closure Sg, Relation.ReflTransGen R m₀ (g • m₀) := by
  have hmap : ∀ g ∈ Subgroup.closure Sg, ∀ a b, Relation.ReflTransGen R a b →
      Relation.ReflTransGen R (g • a) (g • b) := by
    intro g hg a b h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (hinv g hg _ _ hbc)
  have hsymm : ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ hbc ih => exact (Relation.ReflTransGen.single (hsym _ _ hbc)).trans ih
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    rcases hgen s hs with e | e
    · rw [e]
    · exact Relation.ReflTransGen.single e
  | one => rw [one_smul]
  | mul g g' hg hg' ih ih' =>
    rw [mul_smul]
    exact ih.trans (hmap g hg _ _ ih')
  | inv g hg ih =>
    have h := hmap g⁻¹ (inv_mem hg) _ _ ih
    rw [inv_smul_smul] at h
    exact hsymm _ _ h

theorem smul_set_eq {α G : Type*} [Group G] [MulAction G α] {Y : Set α} (hY : Y.Finite) {g : G}
    (h : ∀ V ∈ Y, g • V ∈ Y) : g • Y = Y := by
  have hsub : g • Y ⊆ Y := by
    rintro _ ⟨V, hV, rfl⟩
    exact h V hV
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_smul_set]) hY

theorem orbit_sub {α G : Type*} [Group G] [Finite G] [MulAction G α] {Gab : Set G} {T : α}
    {X : Set α} (hT : T ∈ X) (hX : ∀ γ ∈ Gab, ∀ V ∈ X, γ • V ∈ X) :
    ∀ g ∈ Subgroup.closure Gab, g • T ∈ X := by
  set Y : Set α := X ∩ Set.range fun g : G => g • T
  have hY : Y.Finite := (Set.finite_range _).subset Set.inter_subset_right
  have hle : Subgroup.closure Gab ≤ MulAction.stabilizer G Y := by
    rw [Subgroup.closure_le]
    intro γ hγ
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    refine smul_set_eq hY fun V hV => ⟨hX γ hγ V hV.1, ?_⟩
    obtain ⟨g, rfl⟩ := hV.2
    exact ⟨γ * g, mul_smul _ _ _⟩
  intro g hg
  have h := MulAction.mem_stabilizer_iff.1 (hle hg)
  have hT' : g • T ∈ g • Y := Set.smul_mem_smul_set ⟨hT, 1, one_smul _ _⟩
  rw [h] at hT'
  exact hT'.1

theorem perm_apply_inv (g : Equiv.Perm P) (x : P) : g (g⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem perm_inv_apply (g : Equiv.Perm P) (x : P) : g⁻¹ (g x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

namespace TSys

variable {A : Subgroup (Equiv.Perm P)} {τ : P → Equiv.Perm P} (hs : TSys A τ)
include hs

theorem inv (x : P) : (τ x)⁻¹ = τ x := inv_eq_of_mul_eq_one_right (hs.sq x)

theorem self (x : P) : τ x x = x := by
  apply hs.inj
  rw [hs.conj _ (hs.mem x), hs.inv, hs.sq, one_mul]

theorem conj_self (y x : P) : τ (τ y x) = τ y * τ x * τ y := by
  rw [hs.conj _ (hs.mem y), hs.inv]

theorem conj_inv {g : Equiv.Perm P} (hg : g ∈ A) (x : P) : τ x = g * τ (g⁻¹ x) * g⁻¹ := by
  rw [← hs.conj g hg, perm_apply_inv]

theorem mem_smul_self {V : Finset P} {h : P} : h ∈ τ h • V ↔ h ∈ V := by
  rw [← Finset.inv_smul_mem_iff, hs.inv, Equiv.Perm.smul_def, hs.self]

theorem mem_τ_smul {V : Finset P} {h y : P} : y ∈ τ h • V ↔ τ h y ∈ V := by
  rw [← Finset.inv_smul_mem_iff, hs.inv, Equiv.Perm.smul_def]

theorem τ_τ (h : P) (V : Finset P) : τ h • τ h • V = V := by
  rw [smul_smul, hs.sq, one_smul]

theorem adj_symm {V W : Finset P} (h : Adj τ V W) : Adj τ W V := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, by rwa [hs.mem_smul_self], (hs.τ_τ x V).symm⟩

theorem adj_smul {g : Equiv.Perm P} (hg : g ∈ A) {V W : Finset P} (h : Adj τ V W) :
    Adj τ (g • V) (g • W) := by
  obtain ⟨x, hx, rfl⟩ := h
  refine ⟨g x, ?_, ?_⟩
  · rw [← Equiv.Perm.smul_def, Finset.smul_mem_smul_finset_iff]
    exact hx
  · rw [hs.conj g hg, smul_smul, smul_smul, inv_mul_cancel_right]

theorem adj_smul_iff {g : Equiv.Perm P} (hg : g ∈ A) {V W : Finset P} :
    Adj τ (g • V) (g • W) ↔ Adj τ V W := by
  refine ⟨fun h => ?_, hs.adj_smul hg⟩
  have h' := hs.adj_smul (inv_mem hg) h
  rwa [inv_smul_smul, inv_smul_smul] at h'

theorem closure_le (X : Set P) : Subgroup.closure (τ '' X) ≤ A := by
  rw [Subgroup.closure_le]
  rintro _ ⟨x, -, rfl⟩
  exact hs.mem x

omit hs in
theorem fix_closure {X : Set P} {V : Finset P} (hX : ∀ s ∈ X, τ s • V = V) {g : Equiv.Perm P}
    (hg : g ∈ Subgroup.closure (τ '' X)) : g • V = V := by
  have hle : Subgroup.closure (τ '' X) ≤ MulAction.stabilizer (Equiv.Perm P) V := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs', rfl⟩
    exact MulAction.mem_stabilizer_iff.2 (hX s hs')
  exact MulAction.mem_stabilizer_iff.1 (hle hg)

omit hs in
theorem fix_closure_pt {X : Set P} {y : P} (hX : ∀ s ∈ X, τ s y = y) {g : Equiv.Perm P}
    (hg : g ∈ Subgroup.closure (τ '' X)) : g y = y := by
  have hle : Subgroup.closure (τ '' X) ≤ MulAction.stabilizer (Equiv.Perm P) y := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs', rfl⟩
    exact MulAction.mem_stabilizer_iff.2 (hX s hs')
  exact MulAction.mem_stabilizer_iff.1 (hle hg)

theorem smul_τ {g : Equiv.Perm P} (hg : g ∈ A) {T : Finset P} (hT : g • T = T) (f : P) :
    g • τ f • T = τ (g f) • T := by
  rw [hs.conj g hg, mul_smul, mul_smul]
  congr 2
  rw [← hT, inv_smul_smul, hT]

theorem not_mem_smul {g : Equiv.Perm P} {T : Finset P} (hT : g • T = T) {f : P} (hf : f ∉ T) :
    g f ∉ T := by
  rw [← hT, ← Equiv.Perm.smul_def, Finset.smul_mem_smul_finset_iff]
  exact hf

section Q

variable {T : Finset P} {S : Set P} {x0 : P}
  (hS : ∀ s ∈ S, τ s • T = T) (h0 : τ x0 • T = T) (hcov : ∀ x ∈ T, x ∈ Orb τ S x0)
include hS h0 hcov

theorem fix_T {x : P} (hx : x ∈ T) : τ x • T = T := by
  obtain ⟨g, hg, rfl⟩ := hcov x hx
  rw [hs.conj g (hs.closure_le S hg), mul_smul, mul_smul, fix_closure hS (inv_mem hg), h0,
    fix_closure hS hg]

theorem fix_mem {g : Equiv.Perm P} (hg : g ∈ A) {x : P} (hx : x ∈ g • T) :
    τ x • (g • T) = g • T := by
  have hx' : g⁻¹ • x ∈ T := Finset.inv_smul_mem_iff.2 hx
  rw [hs.conj_inv hg x, mul_smul, mul_smul, inv_smul_smul, ← Equiv.Perm.smul_def,
    hs.fix_T hS h0 hcov hx']

theorem q_eq {g : Equiv.Perm P} (hg : g ∈ A) (hx0 : x0 ∈ g • T) (hSg : ∀ s ∈ S, s ∈ g • T) :
    g • T = T := by
  have hfix : ∀ h ∈ Subgroup.closure (τ '' S), h • (g • T) = g • T := fun h hh =>
    fix_closure (fun s hs' => hs.fix_mem hS h0 hcov hg (hSg s hs')) hh
  have hsub : T ⊆ g • T := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := hcov x hx
    rw [← hfix h hh, ← Equiv.Perm.smul_def]
    exact Finset.smul_mem_smul_finset hx0
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])).symm

theorem τ_mem_H (hST : S ⊆ T) {s1 : P} (hs1 : s1 ∈ S) {x : P} (hx : x ∈ T) :
    τ x ∈ Subgroup.closure (τ '' S) := by
  have key : ∀ g ∈ Subgroup.closure (τ '' S), ∀ y, τ (g y) = g * τ y * g⁻¹ :=
    fun g hg y => hs.conj g (hs.closure_le S hg) y
  obtain ⟨g, hg, hgx⟩ := hcov s1 (hST hs1)
  have h0mem : τ x0 ∈ Subgroup.closure (τ '' S) := by
    have e : τ x0 = g⁻¹ * τ s1 * g := by
      rw [← hgx, key g hg]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hg) (Subgroup.subset_closure ⟨s1, hs1, rfl⟩)) hg
  obtain ⟨h, hh, rfl⟩ := hcov x hx
  rw [key h hh]
  exact mul_mem (mul_mem hh h0mem) (inv_mem hh)

end Q

end TSys

end CertificateChecks.KernelFi23T

end
