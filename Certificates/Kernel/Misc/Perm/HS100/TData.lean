module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Native.ChainCentralizer
meta import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CertificateChecks.KernelMisc.HS100.T

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def tL : List (Array Nat) := zasTGens.toList

meta def eL (j : Nat) : List (Array Nat) := (zasEGens j).toList

meta def e0 : List (Array Nat) := eL 0
meta def e1 : List (Array Nat) := eL 1
meta def e2 : List (Array Nat) := eL 2
meta def e3 : List (Array Nat) := eL 3
meta def e4 : List (Array Nat) := eL 4
meta def e5 : List (Array Nat) := eL 5
meta def e6 : List (Array Nat) := eL 6
meta def e7 : List (Array Nat) := eL 7

meta def keyOf (a : Array Nat) : Nat := zasTKeys.foldr (fun p acc => a[p]! + 100 * acc) 0

meta def tKey : List Nat :=
  let pts := (search 100 7 tL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def tInv : List Nat :=
  let pts := (search 100 7 tL.toArray).1
  let idp := Array.ofFn (n := 100) fun i => i.val
  (List.range pts.size).filter fun i => comp 100 pts[i]! pts[i]! == idp && pts[i]! != idp

end CertificateChecks.KernelMisc.HS100.T

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.HS100.T.TX CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasTHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.T.TX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasTHex 3 100 7 3
#ks_chars CertificateChecks.KernelMisc.HS100.T.EA CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasEHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.T.EA
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasEHex 3 100 7 32

#lc_bfs CertificateChecks.KernelMisc.HS100.T.TT CertificateChecks.KernelMisc.HS100.T.tL 100 7
#kss_natlist CertificateChecks.KernelMisc.HS100.T.TTK CertificateChecks.KernelMisc.HS100.T.tKey
#kss_natlist CertificateChecks.KernelMisc.HS100.T.TTI CertificateChecks.KernelMisc.HS100.T.tInv

#lc_bfs CertificateChecks.KernelMisc.HS100.T.E0 CertificateChecks.KernelMisc.HS100.T.e0 100 7

#lc_bfs CertificateChecks.KernelMisc.HS100.T.E1 CertificateChecks.KernelMisc.HS100.T.e1 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.T.E2 CertificateChecks.KernelMisc.HS100.T.e2 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.T.E3 CertificateChecks.KernelMisc.HS100.T.e3 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.T.E4 CertificateChecks.KernelMisc.HS100.T.e4 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.T.E5 CertificateChecks.KernelMisc.HS100.T.e5 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.T.E6 CertificateChecks.KernelMisc.HS100.T.e6 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.T.E7 CertificateChecks.KernelMisc.HS100.T.e7 100 7
