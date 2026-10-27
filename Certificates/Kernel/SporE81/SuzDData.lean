module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
meta import Certificates.Kernel.Sporadic.RawGen
public import Std.Data.HashMap

namespace CertificateChecks.KernelE81.SuzDE

open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

meta def gens (t : Nat) : List (Array Nat) :=
  (suzE81.dW[t]!.map (posWord 1782 (qGens suzE81))).toList

meta def g0 : List (Array Nat) := gens 0
meta def g1 : List (Array Nat) := gens 1
meta def g2 : List (Array Nat) := gens 2
meta def g3 : List (Array Nat) := gens 3
meta def g4 : List (Array Nat) := gens 4
meta def g5 : List (Array Nat) := gens 5
meta def g6 : List (Array Nat) := gens 6
meta def g7 : List (Array Nat) := gens 7
meta def g8 : List (Array Nat) := gens 8
meta def g9 : List (Array Nat) := gens 9

meta def keyOf (ps : List Nat) (a : Array Nat) : Nat :=
  ps.foldr (fun p acc => a[p]! + 1782 * acc) 0

meta def pts (gs : List (Array Nat)) : Array (Array Nat) :=
  (CFSG.KC.BfsGen.search 1782 11 gs.toArray).1

meta def kD (t : Nat) : List Nat :=
  let p := pts (gens t)
  ((Array.range p.size).qsort fun a b =>
    keyOf suzE81.dKeys p[a]! < keyOf suzE81.dKeys p[b]!).toList

meta def k0 : List Nat := kD 0
meta def k1 : List Nat := kD 1
meta def k2 : List Nat := kD 2
meta def k3 : List Nat := kD 3
meta def k4 : List Nat := kD 4
meta def k5 : List Nat := kD 5
meta def k6 : List Nat := kD 6
meta def k7 : List Nat := kD 7
meta def k8 : List Nat := kD 8
meta def k9 : List Nat := kD 9

meta def dIdx : Array (Std.HashMap Nat Nat) :=
  (Array.range 10).map fun t =>
    let p := pts (gens t)
    (List.range p.size).foldl (fun m j => m.insert (CFSG.KS.RawGen.pack 11 p[j]!) j) {}

meta def idx1 (t : Nat) (a : Array Nat) : Nat :=
  match dIdx[t]!.get? (CFSG.KS.RawGen.pack 11 a) with
  | some j => j + 1
  | none => 0

meta def zw : List Nat := (List.range 10).map fun t => idx1 t (zArr suzE81)

meta def cw : List Nat :=
  let z := zArr suzE81
  let z2 := compA 1782 z z
  let id := idA 1782
  let zs := zw.toArray
  (pts (qGens suzE81).toList).toList.map fun s =>
    if eqA 1782 s z || eqA 1782 s z2 || eqA 1782 s id then 0
    else
      match (List.range 1782).find? (fun x => s[s[s[x]!]!]! != x) with
      | some x => 1 + x
      | none =>
        match (List.range 10).find? (fun t => decide (0 < zs[t]!) && decide (0 < idx1 t s)) with
        | some t => 1 + 1782 + t + 10 * (idx1 t s - 1)
        | none => 0

end CertificateChecks.KernelE81.SuzDE

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelE81.S9D0 CertificateChecks.KernelE81.SuzDE.g0 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D1 CertificateChecks.KernelE81.SuzDE.g1 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D2 CertificateChecks.KernelE81.SuzDE.g2 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D3 CertificateChecks.KernelE81.SuzDE.g3 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D4 CertificateChecks.KernelE81.SuzDE.g4 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D5 CertificateChecks.KernelE81.SuzDE.g5 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D6 CertificateChecks.KernelE81.SuzDE.g6 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D7 CertificateChecks.KernelE81.SuzDE.g7 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D8 CertificateChecks.KernelE81.SuzDE.g8 1782 11
#lc_bfs CertificateChecks.KernelE81.S9D9 CertificateChecks.KernelE81.SuzDE.g9 1782 11
#kss_natlist CertificateChecks.KernelE81.S9D0.SKT CertificateChecks.KernelE81.SuzDE.k0
#kss_natlist CertificateChecks.KernelE81.S9D1.SKT CertificateChecks.KernelE81.SuzDE.k1
#kss_natlist CertificateChecks.KernelE81.S9D2.SKT CertificateChecks.KernelE81.SuzDE.k2
#kss_natlist CertificateChecks.KernelE81.S9D3.SKT CertificateChecks.KernelE81.SuzDE.k3
#kss_natlist CertificateChecks.KernelE81.S9D4.SKT CertificateChecks.KernelE81.SuzDE.k4
#kss_natlist CertificateChecks.KernelE81.S9D5.SKT CertificateChecks.KernelE81.SuzDE.k5
#kss_natlist CertificateChecks.KernelE81.S9D6.SKT CertificateChecks.KernelE81.SuzDE.k6
#kss_natlist CertificateChecks.KernelE81.S9D7.SKT CertificateChecks.KernelE81.SuzDE.k7
#kss_natlist CertificateChecks.KernelE81.S9D8.SKT CertificateChecks.KernelE81.SuzDE.k8
#kss_natlist CertificateChecks.KernelE81.S9D9.SKT CertificateChecks.KernelE81.SuzDE.k9
#kss_natlist CertificateChecks.KernelE81.S9ZW CertificateChecks.KernelE81.SuzDE.zw
#kss_natlist CertificateChecks.KernelE81.S9CW CertificateChecks.KernelE81.SuzDE.cw

end
