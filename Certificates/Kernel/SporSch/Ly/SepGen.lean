module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.SporSch.Ly.GenLy
public meta import CFSG.Sporadic.Schreier.LyCheckSep
public meta import CFSG.RankThree.Native.LySeedCheckInputs
public import Certificates.Kernel.SporSch.Ly.GenLy
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

namespace CertificateChecks.KernelSporSch.LySepGen

open CFSG.KC.Eval CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.KS.SporSch.LyGen
open CFSG.Sporadic.LySchreier.Native

meta def matOf (f : Nat → Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 111) fun j => f i.val j.val

meta def packDigits (ds : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for t in [0:ds.size] do
    acc := acc ||| (ds[t]! <<< (1332 * (t / 111) + 12 * (t % 111)))
  return acc

meta def keyVals (k : ByteArray) : Nat × Nat × Nat :=
  let pEnt (j a : Nat) : Nat := if a < 7 then keyDigit k (111 * a + j) else 0
  let cEnt (a b : Nat) : Nat := if a < 7 && b < 7 then keyDigit k (777 + 7 * a + b) else 0
  (packM (matOf fun a j => pEnt j a), packM (matOf pEnt), packM (matOf cEnt))

public meta def sepStep (args : Array Val) : Except String (Array (Lean.Name × Val)) :=
  if args.size != 0 then .error "sepStep: expected no arguments" else
  let kd : Array Nat := (txtLines sepKeysTxt).foldl (fun acc s => acc ++ digitsOf s) #[]
  let kv := sepKeys.map keyVals
  let Z := faithZ sepKeys formF
  let cb := colsMat 111 (cyclicVecs Z sepV sepPar sepOp)
  let vw := packDigits (sepV ++ Array.replicate (111 - sepV.size) 0 ++ sepW)
  let lines := txtLines sepTreeTxt
  let natsV (a : Array Nat) : Val := .list (a.map Val.nat)
  .ok #[(`KK, .nat (packDigits kd)), (`PLT, .list (kv.map fun x => .nat x.1)),
    (`PL, .list (kv.map fun x => .nat x.2.1)), (`CL, .list (kv.map fun x => .nat x.2.2)),
    (`Y, .nat (packM sepY)), (`CI, .nat (packM sepCinv)), (`CB, .nat (packM cb)),
    (`VW, .nat vw), (`PAR, natsV sepPar), (`OP, natsV sepOp),
    (`L2, natsV (parseNats (lines.getD 2 "")))]

end CertificateChecks.KernelSporSch.LySepGen
