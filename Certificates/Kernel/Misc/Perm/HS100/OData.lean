module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData2
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData2
meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData

public section

namespace CertificateChecks.KernelMisc.HS100.O

open CFSG.EvenSporadicStandard.HSStd
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def sL : List (Array Nat) := s5oSGens.toList

meta def keyOf (a : Array Nat) : Nat := s5Keys.foldr (fun p acc => a[p]! + 100 * acc) 0

meta def sKey : List Nat :=
  let pts := (search 100 7 sL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelMisc.HS100.O

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.HS100.O.OX CFSG.EvenSporadicStandard.HSStd.s5oHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.O.OX CFSG.EvenSporadicStandard.HSStd.s5oHex 3 100 7 16
#ks_chars CertificateChecks.KernelMisc.HS100.O.FX CFSG.EvenSporadicStandard.HSStd.s5fHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.O.FX CFSG.EvenSporadicStandard.HSStd.s5fHex 3 100 7 19
#ks_chars CertificateChecks.KernelMisc.HS100.O.KX CFSG.EvenSporadicStandard.HSStd.s5fKHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.O.KX CFSG.EvenSporadicStandard.HSStd.s5fKHex 2 1024 8 1
#ks_chars CertificateChecks.KernelMisc.HS100.O.JX CFSG.EvenSporadicStandard.HSStd.s5fJHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.O.JX CFSG.EvenSporadicStandard.HSStd.s5fJHex 3 1024 12 1

#lc_bfs CertificateChecks.KernelMisc.HS100.O.OS CertificateChecks.KernelMisc.HS100.O.sL 100 7
#kss_natlist CertificateChecks.KernelMisc.HS100.O.OSK CertificateChecks.KernelMisc.HS100.O.sKey
