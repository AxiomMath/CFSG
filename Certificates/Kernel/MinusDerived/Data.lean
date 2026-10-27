module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedData
public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedData
public meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.BfsGen CFSG.KS.RawGen

meta def gL : List (Array Nat) := minusLGens.toList

meta def keyOf (a : Array Nat) : Nat := minusBase.foldr (fun p acc => a[p]! + 65 * acc) 0

meta def kl : List Nat :=
  let pts := (search 65 7 gL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelMinusL

end

set_option maxRecDepth 400000

#lc_bfs_sl CertificateChecks.KernelMinusL.PL CertificateChecks.KernelMinusL.gL 65 7 520

#kss_natlist CertificateChecks.KernelMinusL.KL CertificateChecks.KernelMinusL.kl
