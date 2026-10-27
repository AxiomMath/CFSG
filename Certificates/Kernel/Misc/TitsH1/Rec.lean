module

public meta import Lean
meta import CFSG.Quasithin.H13.L32NKGCertInputs
meta import Certificates.Data.TitsR2V6
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
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

namespace CFSG.KD.TitsH1.Gen

open CFSG.Quasithin.H13.KGCert

meta def c64 (x : List Nat) : Nat := (x ++ [64, 128]).foldr (fun c acc => c + 256 * acc) 0

meta def mulM (A B : Nat) : Nat := Id.run do
  let mut r := 0
  for j in [0:8] do
    let b := (B >>> (8 * j)) &&& 255
    let mut col := 0
    for i in [0:8] do
      if (b >>> i) &&& 1 == 1 then
        col := col ^^^ ((A >>> (8 * i)) &&& 255)
    r := r ||| (col <<< (8 * j))
  return r

meta def mvM (A v : Nat) : Nat := Id.run do
  let mut r := 0
  for i in [0:6] do
    if (v >>> i) &&& 1 == 1 then
      r := r ^^^ ((A >>> (8 * i)) &&& 255)
  return r

meta def gA : Nat := c64 gAc
meta def gB : Nat := c64 gBc
meta def oneM : Nat := c64 oneC

meta def esdM : Array Nat × Array Nat × Std.HashMap Nat Nat := Id.run do
  let mut es : Array Nat := #[oneM]
  let mut ds : Array Nat := #[0]
  let mut idx : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert oneM 0
  let mut fr : List Nat := [0]
  for _ in [0:200] do
    if fr.isEmpty then break
    let mut nf : List Nat := []
    for t in fr do
      for (g, gd) in [(gA, 15), (gB, 0)] do
        let y := mulM g es[t]!
        if !idx.contains y then
          idx := idx.insert y es.size
          nf := es.size :: nf
          es := es.push y
          ds := ds.push (gd ^^^ mvM g ds[t]!)
    fr := nf
  return (es, ds, idx)

meta def recM : List Nat :=
  esdM.2.1.toList ++ [esdM.2.2.getD (c64 Certificates.TitsR2V6.u33Ac) 65535]

end CFSG.KD.TitsH1.Gen

#kss_ntree CFSG.KD.TitsH1.DR CFSG.KD.TitsH1.Gen.recM
