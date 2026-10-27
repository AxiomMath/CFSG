module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2ModelData
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2ModelData
meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
public import CFSG.RankThree.Native.ChainCentralizer
meta import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CertificateChecks.KernelMisc.HS100.N

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def nL : List (Array Nat) := zasNGens.toList

meta def keyOf (a : Array Nat) : Nat := zasNKeys.foldr (fun p acc => a[p]! + 100 * acc) 0

meta def nKey : List Nat :=
  let pts := (search 100 7 nL.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

end CertificateChecks.KernelMisc.HS100.N

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.HS100.N.NX CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasNHex
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.N.NX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.zasNHex 3 100 7 2

#kmisc_packarrs CertificateChecks.KernelMisc.HS100.N.RX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2.i2R 7

#lc_bfs CertificateChecks.KernelMisc.HS100.N.NN CertificateChecks.KernelMisc.HS100.N.nL 100 7

#kss_natlist CertificateChecks.KernelMisc.HS100.N.NNK CertificateChecks.KernelMisc.HS100.N.nKey
