module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0Data
meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Native.FiveKit
meta import CFSG.RankThree.Native.FiveKit

public section

namespace CertificateChecks.KernelMisc.HS100.S0

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0 CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def kL : List (Array Nat) := xGens.toList

meta def cyL : List (Array Nat) := cyGens.toList

meta def aL : List (Array Nat) := aGens.toList

meta def cuL : List (Array Nat) := cuGens.toList

meta def jL : List (Array Nat) := jGens.toList

meta def eL : List (Array Nat) := zasE0Gens.toList

meta def keyOf (a : Array Nat) : Nat := keys.foldr (fun p acc => a[p]! + 100 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 100 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def kKey : List Nat := keyOrder kL

meta def cyKey : List Nat := keyOrder cyL

meta def aKey : List Nat := keyOrder aL

meta def cuKey : List Nat := keyOrder cuL

meta def jKey : List Nat := keyOrder jL

end CertificateChecks.KernelMisc.HS100.S0

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.HS100.S0.SX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.hexData
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.S0.SX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.hexData 3 100 7 11
#ks_chars CertificateChecks.KernelMisc.HS100.S0.ZX CFSG.EvenSporadicStandard.HSStd.s5Hex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.S0.ZX CFSG.EvenSporadicStandard.HSStd.s5Hex 3 100 7 5
#ks_chars CertificateChecks.KernelMisc.HS100.S0.EX CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasEHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.S0.EX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasEHex 3 100 7 4

#lc_bfs CertificateChecks.KernelMisc.HS100.S0.KK CertificateChecks.KernelMisc.HS100.S0.kL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.S0.CY CertificateChecks.KernelMisc.HS100.S0.cyL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.S0.AB CertificateChecks.KernelMisc.HS100.S0.aL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.S0.CB CertificateChecks.KernelMisc.HS100.S0.cuL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.S0.JJ CertificateChecks.KernelMisc.HS100.S0.jL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.S0.E0 CertificateChecks.KernelMisc.HS100.S0.eL 100 7

#kss_natlist CertificateChecks.KernelMisc.HS100.S0.KKK CertificateChecks.KernelMisc.HS100.S0.kKey
#kss_natlist CertificateChecks.KernelMisc.HS100.S0.CYK CertificateChecks.KernelMisc.HS100.S0.cyKey
#kss_natlist CertificateChecks.KernelMisc.HS100.S0.ABK CertificateChecks.KernelMisc.HS100.S0.aKey
#kss_natlist CertificateChecks.KernelMisc.HS100.S0.CBK CertificateChecks.KernelMisc.HS100.S0.cuKey
#kss_natlist CertificateChecks.KernelMisc.HS100.S0.JJK CertificateChecks.KernelMisc.HS100.S0.jKey

#conj_orb CertificateChecks.KernelMisc.HS100.S0.ZO
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.pGens 100 7
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys 525
  roots CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.z0 gens 2
#conj_orb CertificateChecks.KernelMisc.HS100.S0.UO
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.pGens 100 7
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.keys 700
  roots CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S0.u0 gens 2
