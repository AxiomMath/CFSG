module

public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.PartOne.K133Spor.GBarInputs
meta import CFSG.RankThree.PartOne.K133Spor.GBarInputs
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.HNOddCore.QCheckInputs

namespace CertificateChecks.KernelK133.GBarE

public meta def gens : List (Array Nat) := CFSG.Sporadic.HNOddCore.Native.colPerms.toList

meta def keyOf (a : Array Nat) : Nat := [4, 1, 8, 16].foldr (fun p acc => a[p]! + 256 * acc) 0

meta def keyOrder : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 256 9 gens.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelK133.GBarE

public section

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelK133.GB CertificateChecks.KernelK133.GBarE.gens 256 9 400
#kss_natlist CertificateChecks.KernelK133.GB.SKT CertificateChecks.KernelK133.GBarE.keyOrder

end
