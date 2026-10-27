module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameCheck
public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameCheck
meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusFrame
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def t0L : List (Array Nat) := t0Gens.toList

meta def l0L : List (Array Nat) := l0Gens.toList

meta def aL : List (Array Nat) := aGens.toList

meta def keyOf (a : Array Nat) : Nat := minusBase.foldr (fun p acc => a[p]! + 65 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 65 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def k0 : List Nat := keyOrder t0L

meta def kl : List Nat := keyOrder l0L

meta def ka : List Nat := keyOrder aL

meta def wa : Array (Array Nat) :=
  let as := (search 65 7 aGens).1
  let N := as.size
  let idx : Std.HashMap Nat Nat := (Array.range N).foldl (fun m i => m.insert (pack 7 as[i]!) i) {}
  as.map fun ak => Id.run do
    let mut rs : Array Nat := Array.replicate N 0
    if ak == Array.range 65 then return rs
    let cs := as.map fun aj => comp 65 aj (comp 65 ak (inv 65 aj))
    let mut seen : Array Bool := (Array.replicate N false).set! 0 true
    let mut q : Array Nat := #[0]
    let mut h := 0
    while h < q.size do
      let p := q[h]!
      for j in [0:N] do
        let y := comp 65 cs[j]! as[p]!
        let i := idx.getD (pack 7 y) 0
        if !seen[i]! then
          seen := seen.set! i true
          rs := rs.set! i (j + 64 * p + 4096 * (rs[p]! / 4096 + 1))
          q := q.push i
      h := h + 1
    return rs

end CertificateChecks.KernelMinusFrame

end

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelMinusFrame.S0 CertificateChecks.KernelMinusFrame.t0L 65 7
#lc_bfs CertificateChecks.KernelMinusFrame.SL CertificateChecks.KernelMinusFrame.l0L 65 7
#lc_bfs CertificateChecks.KernelMinusFrame.SA CertificateChecks.KernelMinusFrame.aL 65 7

#kss_natlist CertificateChecks.KernelMinusFrame.K0 CertificateChecks.KernelMinusFrame.k0
#kss_natlist CertificateChecks.KernelMinusFrame.KL CertificateChecks.KernelMinusFrame.kl
#kss_natlist CertificateChecks.KernelMinusFrame.KA CertificateChecks.KernelMinusFrame.ka

#kmisc_packarrs CertificateChecks.KernelMinusFrame.WA CertificateChecks.KernelMinusFrame.wa 16
