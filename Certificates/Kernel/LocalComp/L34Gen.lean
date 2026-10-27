module

public import Certificates.Kernel.LocalComp.BfsGen
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelLC.L34Gen

open CFSG.PSL3Four.Native
open CFSG.KS.RawGen (pack)

meta def chunks (k : Nat) (a : Array Nat) : Array (Array Nat) :=
  (Array.range ((a.size + k - 1) / k)).map fun j => a.extract (k * j) (k * j + k)

meta def searchSt (ng : Nat) (st : Nat → Array Nat → Array Nat) (root : Array Nat) :
    Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut pts : Array (Array Nat) := #[root]
  let mut idx : Std.HashMap (Array Nat) Nat := ({} : Std.HashMap (Array Nat) Nat).insert root 0
  let mut edges : Array (Array Nat) := #[]
  let mut i := 0
  while i < pts.size do
    let mut row := #[]
    for k in [0:ng] do
      let y := st k pts[i]!
      match idx.get? y with
      | some j => row := row.push j
      | none =>
        idx := idx.insert y pts.size
        row := row.push pts.size
        pts := pts.push y
    edges := edges.push row
    i := i + 1
  return (pts, edges)

meta def layout (pts edges : Array (Array Nat)) (ew L : Nat) :
    Array (Array Nat) × Array (Array Nat) × Array (Array Nat) × Array (Array Nat) ×
      Array (Array Nat) :=
  let tv := pts.map (pack 6)
  let order := (Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!
  let inv := Id.run do
    let mut r := Array.replicate order.size 0
    for k in [0:order.size] do
      r := r.set! order[k]! k
    return r
  let K := (pts.size + L - 1) / L
  let counts := (Array.range (K + 1)).map fun s =>
    #[(edges.extract 0 (L * s)).foldl (fun m r => r.foldl max m) 0 + 1]
  (chunks 8 tv, chunks 16 (edges.map (pack ew)), chunks 16 order, chunks 16 inv, counts)

meta def lst (gs : Array (Array Nat)) (k : Nat) (t : Array Nat) : Array Nat := comp 42 gs[k]! t

meta def rRun : Array (Array Nat) × Array (Array Nat) := searchSt 6 (lst gTabs) (idTab 42)

meta def sRun : Array (Array Nat) × Array (Array Nat) := searchSt 3 (lst gensS) (idTab 42)

meta def rLay := layout rRun.1 rRun.2 18 1344

meta def sLay := layout sRun.1 sRun.2 18 1344

meta def rT : Array (Array Nat) := rLay.1
meta def rE : Array (Array Nat) := rLay.2.1
meta def rS : Array (Array Nat) := rLay.2.2.1
meta def rSI : Array (Array Nat) := rLay.2.2.2.1
meta def rC : Array (Array Nat) := rLay.2.2.2.2
meta def sT : Array (Array Nat) := sLay.1
meta def sE : Array (Array Nat) := sLay.2.1
meta def sS : Array (Array Nat) := sLay.2.2.1
meta def sSI : Array (Array Nat) := sLay.2.2.2.1
meta def sC : Array (Array Nat) := sLay.2.2.2.2

meta def gP : Array (Array Nat) := gTabs.map fun g => #[pack 6 g]

meta def cst (k : Nat) (t : Array Nat) : Array Nat :=
  comp 42 (comp 42 gTabs[k]! t) (invTab 42 gTabs[k]!)

meta def oRun (r : Array Nat) : Array (Array Nat) × Array (Array Nat) := searchSt 6 cst r

meta def oLay (i : Nat) := let o := oRun (rTabs ())[i]!; layout o.1 o.2 11 o.1.size

end CertificateChecks.KernelLC.L34Gen

end
