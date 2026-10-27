module

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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CertificateChecks.KernelFi23C

variable {G K : Type*} [Group G] [Group K]

structure PropHyp (n c : ℕ) (X : ℕ → G) (Y : ℕ → K) (o : ℕ → ℕ → ℕ)
    (gs ork oik tp tg : ℕ → ℕ) : Prop where
  o_lt : ∀ i < n, ∀ j < n, o i j < n
  o_eq : ∀ i < n, ∀ j < n, X (o i j) = X i * X j * (X i)⁻¹
  X_inj : ∀ i < n, ∀ j < n, X i = X j → i = j
  X_inv : ∀ i < n, (X i)⁻¹ = X i
  Y_inv : ∀ i < n, (Y i)⁻¹ = Y i
  gs_lt : ∀ s < c, gs s < n
  row : ∀ s < c, ∀ j < n, Y (o (gs s) j) = Y (gs s) * Y j * (Y (gs s))⁻¹
  root : ork 0 = gs 0
  ork_lt : ∀ t < n, ork t < n
  edge : ∀ t < n, 0 < t → tp t < t ∧ tg t < c ∧ ork t = o (gs (tg t)) (ork (tp t))
  cover : ∀ i < n, oik i < n ∧ ork (oik i) = i

@[expose] def Compat (n : ℕ) (Y : ℕ → K) (o : ℕ → ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ j < n, Y (o i j) = Y i * Y j * (Y i)⁻¹

theorem compat_step {n c : ℕ} {X : ℕ → G} {Y : ℕ → K} {o : ℕ → ℕ → ℕ} {gs ork oik tp tg : ℕ → ℕ}
    (H : PropHyp n c X Y o gs ork oik tp tg) {g i : ℕ} (hg : g < n) (hi : i < n)
    (hcg : Compat n Y o g) (hci : Compat n Y o i) : Compat n Y o (o g i) := by
  intro j hj
  have hj1 := H.o_lt g hg j hj
  have hj2 := H.o_lt i hi _ hj1
  have hgi := H.o_lt g hg i hi
  have e : o (o g i) j = o g (o i (o g j)) := by
    apply H.X_inj _ (H.o_lt _ hgi j hj) _ (H.o_lt g hg _ hj2)
    rw [H.o_eq _ hgi j hj, H.o_eq g hg i hi, H.o_eq g hg _ hj2, H.o_eq i hi _ hj1,
      H.o_eq g hg j hj]
    have hX := H.X_inv g hg
    have hXi := H.X_inv i hi
    rw [hX, hXi]
    simp only [mul_inv_rev, hX, hXi, mul_assoc]
  rw [e, hcg _ hj2, hci _ hj1, hcg _ hj, hcg _ hi]
  have hY := H.Y_inv g hg
  have hYi := H.Y_inv i hi
  simp only [mul_inv_rev, hY, hYi, mul_assoc]

theorem compat_all {n c : ℕ} {X : ℕ → G} {Y : ℕ → K} {o : ℕ → ℕ → ℕ} {gs ork oik tp tg : ℕ → ℕ}
    (H : PropHyp n c X Y o gs ork oik tp tg) (hc : 0 < c) : ∀ i < n, Compat n Y o i := by
  have ht : ∀ t < n, Compat n Y o (ork t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro htn
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · rw [H.root]
        exact H.row 0 hc
      · obtain ⟨hp, hg, he⟩ := H.edge t htn ht0
        rw [he]
        exact compat_step H (H.gs_lt _ hg) (H.ork_lt _ (by omega)) (H.row _ hg)
          (ih _ hp (by omega))
  intro i hi
  obtain ⟨h1, h2⟩ := H.cover i hi
  rw [← h2]
  exact ht _ h1

end CertificateChecks.KernelFi23C

end
