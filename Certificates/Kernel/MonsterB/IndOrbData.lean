
module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Monster.B.Fischer.InducedData
meta import CFSG.Monster.B.Fischer.InducedOrbitChecksInputs
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

namespace CertificateChecks.KernelMonB.IndOrb

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA.Census

meta def flatE (c : NatCert) : Array Nat := c.edges.foldl (· ++ ·) #[]

meta def invL (n : Nat) (P : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate n 0
  for i in [0:P.size] do
    r := r.set! P[i]! i
  return r

meta def wPts : Array Nat := [0, 1, 3, 7].foldl (fun acc s => acc ++ (wCert s).pts) #[]

meta def zPts : Array Nat := [0, 24, 1].foldl (fun acc s => acc ++ (zCert s).pts) #[]

meta def sigInv : Array Nat :=
  indSigma.foldl (fun t p => t.set! p.2 p.1) (Array.replicate 2464 0)

meta def wData : Array (Array Nat) :=
  #[wPts, invL 1024 wPts, flatE (wCert 0), flatE (wCert 1), flatE (wCert 3), flatE (wCert 7),
    sigmaTable]

meta def zData : Array (Array Nat) :=
  #[zPts, invL 2464 zPts, flatE (zCert 0), flatE (zCert 24), flatE (zCert 1), sigInv, tauTable]

end CertificateChecks.KernelMonB.IndOrb

public section

#kmisc_packarrs CertificateChecks.KernelMonB.IW CertificateChecks.KernelMonB.IndOrb.wData 12
#kmisc_packarrs CertificateChecks.KernelMonB.IZ CertificateChecks.KernelMonB.IndOrb.zData 12

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.IG CFSG.Monster.B.Fischer.indM22GenHex
#kmisc_hexflat CertificateChecks.KernelMonB.IG CFSG.Monster.B.Fischer.indM22GenHex 3 3510 12 2

#ks_chars CertificateChecks.KernelMonB.ISg CFSG.Monster.B.Fischer.indSigmaHex
#kmisc_hexflat CertificateChecks.KernelMonB.ISg CFSG.Monster.B.Fischer.indSigmaHex 3 1540 12 1

#ks_chars CertificateChecks.KernelMonB.ITa CFSG.Monster.B.Fischer.indTauHex
#kmisc_hexflat CertificateChecks.KernelMonB.ITa CFSG.Monster.B.Fischer.indTauHex 3 2464 12 1

end
