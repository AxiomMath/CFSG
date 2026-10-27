module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7L39Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7L39Data

public section

namespace CertificateChecks.KernelHSStd.PumpU3

open CFSG.EvenSporadicStandard.HSStd.PumpTC7 CFSG.KC.BfsGen

meta def uL : List (Array Nat) := uGens.toList

meta def keyOf (a : Array Nat) : Nat := tKeys.foldr (fun p acc => a[p]! + 182 * acc) 0

meta def uKey : List Nat :=
  let pts := (search 182 8 uGens).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelHSStd.PumpU3

end

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelHSStd.PumpU3.U CertificateChecks.KernelHSStd.PumpU3.uL 182 8

#kss_natlist CertificateChecks.KernelHSStd.PumpU3.UK CertificateChecks.KernelHSStd.PumpU3.uKey
