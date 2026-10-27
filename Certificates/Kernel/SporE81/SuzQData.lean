module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
meta import Certificates.Kernel.Sporadic.RawGen
public import Std.Data.HashMap

namespace CertificateChecks.KernelE81.SuzE

open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

meta def gQ : List (Array Nat) := (qGens suzE81).toList

meta def keyOf (ps : List Nat) (a : Array Nat) : Nat :=
  ps.foldr (fun p acc => a[p]! + 1782 * acc) 0

meta def keyOrder (ps : List Nat) (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 1782 11 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf ps pts[a]! < keyOf ps pts[b]!).toList

meta def kQ : List Nat := keyOrder suzE81.qKeys gQ

meta def zL : List Nat :=
  let z := zArr suzE81
  [CFSG.KS.RawGen.pack 11 z, CFSG.KS.RawGen.pack 11 (compA 1782 z z)]

end CertificateChecks.KernelE81.SuzE

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelE81.S9Q CertificateChecks.KernelE81.SuzE.gQ 1782 11 243
#kss_natlist CertificateChecks.KernelE81.S9Q.SKT CertificateChecks.KernelE81.SuzE.kQ
#kss_natlist CertificateChecks.KernelE81.S9Z CertificateChecks.KernelE81.SuzE.zL

namespace CertificateChecks.KernelE81

@[expose] noncomputable def S9Q.SK : List Nat := (List.range 2187).map S9Q.SKT

end CertificateChecks.KernelE81

end
