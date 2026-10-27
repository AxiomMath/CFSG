module

public import CFSG.Certificates.Kernel.Orders.Cert
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.Ord

open CFSG.KC.Ord

theorem andB_iff (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem relBounded_spec {L : Nat} : ∀ {v : List (Nat × Bool)},
    List.rec (motive := fun _ => Bool) true
      (fun x _ ih2 => andB (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g L) x) ih2) v =
      true → ∀ x ∈ v, x.1 < L
  | [], _, x, hx => by simp at hx
  | y :: ys, h, x, hx => by
    have h' : andB (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g L) y)
        (List.rec (motive := fun _ => Bool) true
          (fun x _ ih2 => andB (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g L) x)
            ih2) ys) = true := h
    obtain ⟨hy, hys⟩ := (andB_iff _ _).1 h'
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨g, s⟩ := x
      exact Nat.le_of_ble_eq_true hy
    · exact relBounded_spec hys x hx

theorem relsBounded_spec {L : Nat} : ∀ {rels : List (List (Nat × Bool))},
    relsBounded rels L = true → ∀ v ∈ rels, ∀ x ∈ v, x.1 < L
  | [], _, v, hv => by simp at hv
  | r :: rs, h, v, hv => by
    have h' : andB (List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => andB (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g L) x) ih2) r)
        (relsBounded rs L) = true := h
    obtain ⟨h1, h2⟩ := (andB_iff _ _).1 h'
    rcases List.mem_cons.1 hv with rfl | hv
    · exact relBounded_spec h1
    · exact relsBounded_spec h2 v hv

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem decRun_append (F : Nat → Nat) (lb len p d w S RM M : Nat) :
    ∀ (l1 l2 : List Nat) (St : Nat), decRun F lb len p d w S RM M (List.append l1 l2) St =
      decRun F lb len p d w S RM M l2 (decRun F lb len p d w S RM M l1 St)
  | [], _, _ => rfl
  | leaf :: l1, l2, St => by
    change CFSG.KC.Loop.strictN _ (decRun F lb len p d w S RM M (List.append l1 l2)) =
      decRun F lb len p d w S RM M l2 (CFSG.KC.Loop.strictN _ (decRun F lb len p d w S RM M l1))
    rw [strictN_eq, strictN_eq]
    exact decRun_append F lb len p d w S RM M l1 l2 _

theorem coe_dite_mk {n K : Type} [Fintype n] [DecidableEq n] [Field K] (A : Matrix n n K)
    {_ : Decidable (A.det ≠ 0)} (h : A.det ≠ 0) :
    (((if h' : A.det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero A h' else 1 : GL n K)) :
      Matrix n n K) = A := by
  rw [dite_eq_left h]
  rfl

theorem decRun_join {F : Nat → Nat} {lb len p d w S RM M : Nat} {l1 l2 : List Nat} {x y z : Nat}
    (h1 : Nat.beq (decRun F lb len p d w S RM M l1 x) y = true)
    (h2 : Nat.beq (decRun F lb len p d w S RM M l2 y) z = true) :
    Nat.beq (decRun F lb len p d w S RM M (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [decRun_append, h1, h2]

end CFSG.KS.Ord

end
