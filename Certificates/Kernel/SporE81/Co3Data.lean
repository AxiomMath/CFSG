module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo3E81Data
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo3E81Data
meta import Certificates.Kernel.Sporadic.RawGen
public import Std.Data.HashMap

namespace CertificateChecks.KernelE81.Co3E

open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

meta def gQ : List (Array Nat) := (qGens co3E81).toList

meta def gR : List (Array Nat) := (rGens co3E81).toList

meta def gD : List (Array Nat) := (co3E81.dW[0]!.map (posWord 276 (qGens co3E81))).toList

meta def keyOf (ps : List Nat) (a : Array Nat) : Nat := ps.foldr (fun p acc => a[p]! + 276 * acc) 0

meta def keyOrder (ps : List Nat) (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 276 9 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf ps pts[a]! < keyOf ps pts[b]!).toList

meta def kQ : List Nat := keyOrder co3E81.qKeys gQ

meta def kR : List Nat := keyOrder co3E81.rKeys gR

meta def kD : List Nat := keyOrder co3E81.dKeys gD

meta def hL : List Nat := (hArrs co3E81).toList.map (CFSG.KS.RawGen.pack 9)

meta def zL : List Nat :=
  let z := zArr co3E81
  [CFSG.KS.RawGen.pack 9 z, CFSG.KS.RawGen.pack 9 (compA 276 z z)]

meta def idx1 (dp : Std.HashMap Nat Nat) (a : Array Nat) : Nat :=
  match dp.get? (CFSG.KS.RawGen.pack 9 a) with
  | some j => j + 1
  | none => 0

meta def dIdx : Std.HashMap Nat Nat :=
  let dp := (CFSG.KC.BfsGen.search 276 9 gD.toArray).1
  (List.range dp.size).foldl (fun m j => m.insert (CFSG.KS.RawGen.pack 9 dp[j]!) j) {}

meta def zw : List Nat :=
  let hs := hArrs co3E81
  let z := zArr co3E81
  (List.range hs.size).map fun i => idx1 dIdx (conjA 276 hs[i]! z)

meta def cw : List Nat :=
  let hs := hArrs co3E81
  let z := zArr co3E81
  let z2 := compA 276 z z
  let id := idA 276
  let rp := (CFSG.KC.BfsGen.search 276 9 gR.toArray).1
  let zs := zw.toArray
  rp.toList.map fun s =>
    if !eqA 276 (compA 276 s (compA 276 s s)) id || eqA 276 s id || eqA 276 s z || eqA 276 s z2
    then 0
    else
      match (List.range hs.size).find? (fun i =>
          decide (0 < zs[i]!) && decide (0 < idx1 dIdx (conjA 276 hs[i]! s))) with
      | some i => 1 + i + 10 * (idx1 dIdx (conjA 276 hs[i]! s) - 1)
      | none => 0

end CertificateChecks.KernelE81.Co3E

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelE81.C3Q CertificateChecks.KernelE81.Co3E.gQ 276 9
#lc_bfs CertificateChecks.KernelE81.C3R CertificateChecks.KernelE81.Co3E.gR 276 9
#lc_bfs CertificateChecks.KernelE81.C3D CertificateChecks.KernelE81.Co3E.gD 276 9
#kss_natlist CertificateChecks.KernelE81.C3Q.SKT CertificateChecks.KernelE81.Co3E.kQ
#kss_natlist CertificateChecks.KernelE81.C3R.SKT CertificateChecks.KernelE81.Co3E.kR
#kss_natlist CertificateChecks.KernelE81.C3D.SKT CertificateChecks.KernelE81.Co3E.kD
#kss_natlist CertificateChecks.KernelE81.C3H CertificateChecks.KernelE81.Co3E.hL
#kss_natlist CertificateChecks.KernelE81.C3Z CertificateChecks.KernelE81.Co3E.zL
#kss_natlist CertificateChecks.KernelE81.C3ZW CertificateChecks.KernelE81.Co3E.zw
#kss_natlist CertificateChecks.KernelE81.C3CW CertificateChecks.KernelE81.Co3E.cw

namespace CertificateChecks.KernelE81

@[expose] noncomputable def C3Q.SK : List Nat := (List.range 2187).map C3Q.SKT

@[expose] noncomputable def C3R.SK : List Nat := (List.range 729).map C3R.SKT

@[expose] noncomputable def C3D.SK : List Nat := (List.range 243).map C3D.SKT

end CertificateChecks.KernelE81

end
