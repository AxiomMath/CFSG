module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo2E81Data
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo2E81Data
meta import Certificates.Kernel.Sporadic.RawGen
public import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap
meta import Mathlib.GroupTheory.Schreier

namespace CertificateChecks.KernelE81.Co2E

open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

meta def gQ : List (Array Nat) := (qGens co2E81).toList

meta def gD : List (Array Nat) := (co2E81.dW[0]!.map (posWord 2300 (qGens co2E81))).toList

meta def keyOf (ps : List Nat) (a : Array Nat) : Nat := ps.foldr (fun p acc => a[p]! + 2300 * acc) 0

meta def keyOrder (ps : List Nat) (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 2300 12 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf ps pts[a]! < keyOf ps pts[b]!).toList

meta def kQ : List Nat := keyOrder co2E81.qKeys gQ

meta def kD : List Nat := keyOrder co2E81.dKeys gD

meta def hL : List Nat := (hArrs co2E81).toList.map (CFSG.KS.RawGen.pack 12)

meta def zL : List Nat :=
  let z := zArr co2E81
  [CFSG.KS.RawGen.pack 12 z, CFSG.KS.RawGen.pack 12 (compA 2300 z z)]

meta def idx1 (dp : Std.HashMap Nat Nat) (a : Array Nat) : Nat :=
  match dp.get? (CFSG.KS.RawGen.pack 12 a) with
  | some j => j + 1
  | none => 0

meta def dIdx : Std.HashMap Nat Nat :=
  let dp := (CFSG.KC.BfsGen.search 2300 12 gD.toArray).1
  (List.range dp.size).foldl (fun m j => m.insert (CFSG.KS.RawGen.pack 12 dp[j]!) j) {}

meta def zw : List Nat :=
  let hs := hArrs co2E81
  let z := zArr co2E81
  (List.range hs.size).map fun i => idx1 dIdx (conjA 2300 hs[i]! z)

meta def cw : List Nat :=
  let hs := hArrs co2E81
  let z := zArr co2E81
  let z2 := compA 2300 z z
  let id := idA 2300
  let rp := (CFSG.KC.BfsGen.search 2300 12 gQ.toArray).1
  let zs := zw.toArray
  rp.toList.map fun s =>
    if !eqA 2300 (compA 2300 s (compA 2300 s s)) id || eqA 2300 s id || eqA 2300 s z ||
        eqA 2300 s z2
    then 0
    else
      match (List.range hs.size).find? (fun i =>
          decide (0 < zs[i]!) && decide (0 < idx1 dIdx (conjA 2300 hs[i]! s))) with
      | some i => 1 + i + 16 * (idx1 dIdx (conjA 2300 hs[i]! s) - 1)
      | none => 0

end CertificateChecks.KernelE81.Co2E

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelE81.C2Q CertificateChecks.KernelE81.Co2E.gQ 2300 12
#lc_bfs CertificateChecks.KernelE81.C2D CertificateChecks.KernelE81.Co2E.gD 2300 12
#kss_natlist CertificateChecks.KernelE81.C2Q.SKT CertificateChecks.KernelE81.Co2E.kQ
#kss_natlist CertificateChecks.KernelE81.C2D.SKT CertificateChecks.KernelE81.Co2E.kD
#kss_natlist CertificateChecks.KernelE81.C2H CertificateChecks.KernelE81.Co2E.hL
#kss_natlist CertificateChecks.KernelE81.C2Z CertificateChecks.KernelE81.Co2E.zL
#kss_natlist CertificateChecks.KernelE81.C2ZW CertificateChecks.KernelE81.Co2E.zw
#kss_natlist CertificateChecks.KernelE81.C2CW CertificateChecks.KernelE81.Co2E.cw

namespace CertificateChecks.KernelE81

@[expose] noncomputable def C2Q.SK : List Nat := (List.range 729).map C2Q.SKT

@[expose] noncomputable def C2D.SK : List Nat := (List.range 81).map C2D.SKT

end CertificateChecks.KernelE81

end
