module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.FactorsCheck
public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.OddTranspositions.PartThree.Eleven.Plus.FactorsCheck
meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelPlusF

open CFSG.OddTranspositions.PartThree CFSG.KC.BfsGen CFSG.KS.RawGen

meta def plusL : List (Array Nat) := plusTable.toList

meta def aL : List (Array Nat) := plusFactorsAgens.toList

meta def bL : List (Array Nat) := plusFactorsBgens.toList

meta def keyOf (a : Array Nat) : Nat := plusBase.foldr (fun p acc => a[p]! + 60 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 60 6 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def ke : List Nat := keyOrder plusL

meta def ka : List Nat := keyOrder aL

meta def kb : List Nat := keyOrder bL

meta def trees (gs : List (Array Nat)) : Array (Array Nat) :=
  let as := (search 60 6 gs.toArray).1
  let N := as.size
  let idx : Std.HashMap Nat Nat := (Array.range N).foldl (fun m i => m.insert (pack 6 as[i]!) i) {}
  as.map fun ak => Id.run do
    let mut rs : Array Nat := Array.replicate N 0
    if ak == Array.range 60 then return rs
    let cs := as.map fun aj => comp 60 aj (comp 60 ak (inv 60 aj))
    let mut seen : Array Bool := (Array.replicate N false).set! 0 true
    let mut q : Array Nat := #[0]
    let mut h := 0
    while h < q.size do
      let p := q[h]!
      for j in [0:N] do
        let y := comp 60 cs[j]! as[p]!
        let i := idx.getD (pack 6 y) 0
        if !seen[i]! then
          seen := seen.set! i true
          rs := rs.set! i (j + 64 * p + 4096 * (rs[p]! / 4096 + 1))
          q := q.push i
      h := h + 1
    return rs

meta def wa : Array (Array Nat) := trees aL

meta def wb : Array (Array Nat) := trees bL

meta def ie : List Nat :=
  let E := (search 60 6 plusTable).1
  let A := (search 60 6 plusFactorsAgens).1
  let B := (search 60 6 plusFactorsBgens).1
  let id := Array.range 60
  E.toList.map fun x => Id.run do
    if comp 60 x x != id || x == id then return 0
    for i in [0:60] do
      if x == plusTable[i]! then return 1 + i
    for i in [0:60] do
      for j in [0:60] do
        if i != j && (plusTable[i]!)[j]! == j && comp 60 plusTable[i]! plusTable[j]! == x then
          return 61 + i + 60 * j
    for a in [0:A.size] do
      if x == A[a]! then return 3661 + a
    for b in [0:B.size] do
      if x == B[b]! then return 3721 + b
    return 7000000

end CertificateChecks.KernelPlusF

end

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelPlusF.PE CertificateChecks.KernelPlusF.plusL 60 6 240
#lc_bfs CertificateChecks.KernelPlusF.PA CertificateChecks.KernelPlusF.aL 60 6
#lc_bfs CertificateChecks.KernelPlusF.PB CertificateChecks.KernelPlusF.bL 60 6

#kss_natlist CertificateChecks.KernelPlusF.KE CertificateChecks.KernelPlusF.ke
#kss_natlist CertificateChecks.KernelPlusF.KA CertificateChecks.KernelPlusF.ka
#kss_natlist CertificateChecks.KernelPlusF.KB CertificateChecks.KernelPlusF.kb
#kss_natlist CertificateChecks.KernelPlusF.IE CertificateChecks.KernelPlusF.ie

#kmisc_packarrs CertificateChecks.KernelPlusF.WA CertificateChecks.KernelPlusF.wa 16
#kmisc_packarrs CertificateChecks.KernelPlusF.WB CertificateChecks.KernelPlusF.wb 16
