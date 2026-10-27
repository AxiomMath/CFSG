module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.LocalCheck
public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.OddTranspositions.PartThree.Eleven.Minus.LocalCheck
meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelMinusA5

open CFSG.OddTranspositions.PartThree
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def fL : List (Array Nat) := minusA5Gens.toList

meta def keyOf (a : Array Nat) : Nat := minusBase.foldr (fun p acc => a[p]! + 65 * acc) 0

meta def kf : List Nat :=
  let pts := (search 65 7 minusA5Gens).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def wf : Array (Array Nat) :=
  let as := (search 65 7 minusA5Gens).1
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

end CertificateChecks.KernelMinusA5

end

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelMinusA5.SF CertificateChecks.KernelMinusA5.fL 65 7

#kss_natlist CertificateChecks.KernelMinusA5.KF CertificateChecks.KernelMinusA5.kf

#kmisc_packarrs CertificateChecks.KernelMinusA5.WF CertificateChecks.KernelMinusA5.wf 16
