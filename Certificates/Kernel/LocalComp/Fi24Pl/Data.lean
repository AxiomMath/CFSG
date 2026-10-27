module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.HexNumsGen
public import Certificates.Data.Fi24Rank.KData
meta import Certificates.Data.Fi24Rank.KCheck
meta import Certificates.Kernel.LocalComp.BfsGen
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK
import CFSG.Assembly.LowTwoRankDefs
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import Certificates.Kernel.LocalComp.BfsGen
meta import Certificates.Kernel.Sporadic.Fi22.C2068
meta import Certificates.Kernel.Sporadic.Fi22.C3151

namespace CertificateChecks.KernelLC.Fi24PlE

open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

meta def iot : Array (Array Nat) := iotas 504 (kRA ())

meta def pts : Array (Array Nat) :=
  (CFSG.KC.BfsGen.search 504 9 CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NGens).1

meta def base : Array Nat := #[4, 0, 1, 2, 3, 6]

meta def inv (a : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 504 0
  for x in [0:504] do
    r := r.set! a[x]! x
  return r

meta def vRows : Array (Array Nat) := iot.map fun a => let r := inv a; base.map fun b => r[b]!

meta def key (a : Array Nat) : Nat := a.foldr (fun x acc => x + 512 * acc) 0

meta def mRows : Array (Array Nat) := Id.run do
  let A := kRA ()
  let G := CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime.fi24NGens
  let P := pts
  let mut idx : Std.HashMap Nat Nat := {}
  for t in [0:P.size] do
    idx := idx.insert (key P[t]!) t
  let mut out : Array (Array Nat) := #[]
  for k in [0:5] do
    let a := A[k]!
    let ai := inv a
    let mut row := #[]
    for j in [0:12] do
      let g := G[j]!
      let c := Array.ofFn (n := 504) fun x => a[g[ai[x.val]!]!]!
      row := row.push (idx.getD (key c) 65535)
    out := out.push row
  return out

meta def btRows : Array (Array Nat) := Id.run do
  let I := iot
  let V := vRows
  let mut out : Array (Array Nat) := #[]
  for q in pts do
    let mut b := 0
    for i in [0:243] do
      let p := I[i]!
      let v := V[i]!
      if (List.range 6).all fun r => p[q[v[r]!]!]! == q[base[r]!]! then
        b := b ||| (1 <<< i)
    out := out.push #[b]
  return out

end CertificateChecks.KernelLC.Fi24PlE

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.Fi24PlT.A
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.kRAText
#ks_hexnums CertificateChecks.KernelLC.Fi24PlT.A
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative.kRAText 3 9

#kmisc_packarrs CertificateChecks.KernelLC.Fi24PlD.IK CertificateChecks.KernelLC.Fi24PlE.iot 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24PlD.V CertificateChecks.KernelLC.Fi24PlE.vRows 9
#kmisc_packarrs CertificateChecks.KernelLC.Fi24PlD.MK CertificateChecks.KernelLC.Fi24PlE.mRows 16
#kmisc_packarrs CertificateChecks.KernelLC.Fi24PlD.BT CertificateChecks.KernelLC.Fi24PlE.btRows 256

end
