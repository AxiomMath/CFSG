module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Data.HeRCentCheck
meta import Certificates.Data.HePresData
meta import Std.Data.HashMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace CertificateChecks.KernelLC.HeR.SLPGen

open CFSG.ComponentClassification.AS81.HePres.Native

meta def symOf (z : Int) : Nat :=
  if z > 0 then 2 * (z.toNat - 1) else 2 * ((-z).toNat - 1) + 1

meta def subst (p : Nat × Nat) (sym : Nat) (s : Array Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut j := 0
  while j < s.size do
    if j + 1 < s.size && s[j]! == p.1 && s[j + 1]! == p.2 then
      out := out.push sym
      j := j + 2
    else
      out := out.push s[j]!
      j := j + 1
  return out

meta def best (seqs : Array (Array Nat)) : (Nat × Nat) × Nat := Id.run do
  let mut cnt : Std.HashMap (Nat × Nat) Nat := {}
  for s in seqs do
    for i in [0:s.size - 1] do
      let p := (s[i]!, s[i + 1]!)
      cnt := cnt.insert p (cnt.getD p 0 + 1)
  let mut bp := (0, 0)
  let mut bk := 0
  for (p, k) in cnt.toList do
    if k > bk || (k == bk && (p.1 < bp.1 || (p.1 == bp.1 && p.2 < bp.2))) then
      bp := p
      bk := k
  return (bp, bk)

meta def grammar : Array (Nat × Nat) × Array Nat := Id.run do
  let mut seqs : Array (Array Nat) :=
    (hePiHeWords.map fun wd => (wd.map symOf).toArray).toArray
  let mut rules : Array (Nat × Nat) := #[]
  for _ in [0:100000] do
    let (p, k) := best seqs
    if k < 2 then break
    let sym := 4 + rules.size
    rules := rules.push p
    seqs := seqs.map (subst p sym)
  let mut tops : Array Nat := #[]
  for s in seqs do
    let mut t := s[s.size - 1]!
    for i in [0:s.size - 1] do
      rules := rules.push (s[s.size - 2 - i]!, t)
      t := 4 + rules.size - 1
    tops := tops.push t
  return (rules, tops)

meta def gA : Array (Array Nat) := grammar.1.map fun p => #[p.1 ||| (p.2 <<< 16)]

meta def tA : Array (Array Nat) := grammar.2.map fun t => #[t]

meta def vA : Array (Array Nat) := Id.run do
  let n := 8330
  let a := heSeedArrs[0]!
  let b := heSeedArrs[1]!
  let mut vals : Array (Array Nat) :=
    #[a, CFSG.KS.RawGen.inv n a, b, CFSG.KS.RawGen.inv n b]
  for p in grammar.1 do
    vals := vals.push (CFSG.KS.RawGen.comp n vals[p.1]! vals[p.2]!)
  return vals.extract 4 vals.size

end CertificateChecks.KernelLC.HeR.SLPGen

#kmisc_packarrs CertificateChecks.KernelLC.HeR.HSG CertificateChecks.KernelLC.HeR.SLPGen.gA 32
#kmisc_packarrs CertificateChecks.KernelLC.HeR.HST CertificateChecks.KernelLC.HeR.SLPGen.tA 16
#kmisc_packarrs CertificateChecks.KernelLC.HeR.HSV CertificateChecks.KernelLC.HeR.SLPGen.vA 14
