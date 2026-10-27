module

public import Certificates.Data.Kernel.J4Q.QT
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
public import Mathlib.Tactic.ENatToNat
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

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q

@[expose] noncomputable def fstsK {β : Type} (l : List (Nat × β)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun p _ ih => List.cons p.1 ih) l

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allLtK (n : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (Nat.blt x n) ih) l

theorem fstsK_eq {β : Type} : ∀ l : List (Nat × β), fstsK l = l.map Prod.fst
  | [] => rfl
  | p :: l => by
    change p.1 :: fstsK l = _
    rw [fstsK_eq l, List.map_cons]

theorem lenK_eq {α : Type} : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_eq l, List.length_cons]

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem neN_eq (a b : Nat) : neN a b = !Nat.beq a b := by
  unfold neN notB
  cases Nat.beq a b <;> rfl

theorem allLtK_spec {n : Nat} : ∀ {l : List Nat}, allLtK n l = true → ∀ c ∈ l, c < n
  | [], _ => by simp
  | x :: l, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · simpa [Nat.blt_eq] using h1
    · exact allLtK_spec h2 c hc

theorem not_mem_of_allNeK {x : Nat} : ∀ {l : List Nat}, allNeK x l = true → x ∉ l
  | [], _ => by simp
  | y :: l, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    have hne : x ≠ y := by
      intro e
      subst e
      simp [neN, notB, Nat.beq_refl] at h1
    simp only [List.mem_cons, not_or]
    exact ⟨hne, not_mem_of_allNeK h2⟩

theorem nodup_of_distinctK : ∀ {l : List Nat}, distinctK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    exact List.nodup_cons.2 ⟨not_mem_of_allNeK h1, nodup_of_distinctK h2⟩

end CertificateChecks.KernelJ4Q

end
