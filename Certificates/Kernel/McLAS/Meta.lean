module

public meta import CFSG.Sporadic.Recognition.McLASData
public meta import CFSG.Sporadic.Recognition.LyonsAS44McLInputs
public meta import CFSG.Sporadic.Recognition.McLASThreeLocalData
public meta import CFSG.Sporadic.Recognition.LyonsLocalMcLInputs
public meta import CFSG.Sporadic.Schreier.PairMcLCertInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
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

namespace CertificateChecks.KernelMcLAS.M

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275
meta def idsM (k : Nat) : Array (Array Nat) := Array.replicate k idM
meta def invM (a : Array Nat) : Array Nat := CFSG.Monster.B.Co2.Native.invCand 275 a
meta def pgM : Array (Array Nat) :=
  #[CFSG.Sporadic.Schreier.mclStrongArrs[0]!, CFSG.Sporadic.Schreier.mclStrongArrs[1]!]
meta def pgiM : Array (Array Nat) := pgM.map invM
meta def tM (k : Nat) : Array Nat := natArr (threeTbl k)
meta def nM (k : Nat) : Array Nat := natArr (nrmTbl k)
meta def lM (k : Nat) : Array Nat := natArr (tlTbl k)
meta def pairM : Array Nat := natArr pairTbl
meta def x3AM : Array Nat := tM 0
meta def kgM : Array (Array Nat) := #[tM 0, tM 1, tM 2]
meta def kgiM : Array (Array Nat) := kgM.map invM
meta def agM : Array (Array Nat) := #[lM 7, lM 8, lM 9, lM 10]
meta def ids3M : Array (Array Nat) := idsM 3
meta def ids4M : Array (Array Nat) := idsM 4

meta def conjRec (gs gis : Array (Array Nat)) (x : Array Nat) (cap : Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 275 gs[j]! gis[j]! t) gs.size x cap).tabs
meta def mulRec (gs : Array (Array Nat)) (cap : Nat) : Array (Array Nat) :=
  (bfs (fun j t => conjTab 275 idM gs[j]! t) gs.size idM cap).tabs

end CertificateChecks.KernelMcLAS.M

end
