module

public import Certificates.Data.Kernel.Spor.PEnumX
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.PSL3Four.Native

theorem cntBlk_eq (q : Nat → Bool) (b : Nat) : ∀ len, cntBlk q b len = (List.range' b len).countP q
  | 0 => rfl
  | len + 1 => by
    rw [List.range'_concat, Nat.one_mul, List.countP_append, ← cntBlk_eq q b len]
    change strictN (cntBlk q b len) (fun s' => nIf(q (Nat.add b len), Nat.succ s', s')) = _
    rw [strictN_app']
    have e : Nat.add b len = b + len := rfl
    rw [e]
    cases h : q (b + len) <;> simp [h]

theorem cntK_eq (q : Nat → Bool) : ∀ hi, cntK q hi = (List.range (64 * hi)).countP q
  | 0 => rfl
  | hi + 1 => by
    change strictN (cntK q hi) (fun s' => Nat.add s' (cntBlk q (Nat.shiftLeft hi (nat_lit 6))
      (nat_lit 64))) = _
    rw [strictN_app', cntK_eq q hi, cntBlk_eq]
    have e6 : Nat.shiftLeft hi (nat_lit 6) = 64 * hi := by
      change hi <<< 6 = 64 * hi
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e6, Nat.mul_succ, List.range_add, List.countP_append, List.range'_eq_map_range,
      List.countP_map]
    rfl

theorem lget2_eq (L : List (List Nat)) (i : Nat) : lget2 L i = L.getD i [] := by
  induction L generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

end CFSG.KS.PEnum

end
