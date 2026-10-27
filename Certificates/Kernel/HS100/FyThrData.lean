module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Misc.ChainTailQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyThrData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyThrData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.FyE

open CFSG.EvenSporadicStandard.TwoHS

meta def gQ : List (Array Nat) := fyThrQGens.toList

meta def gC : List (Array Nat) := fyThrCGens.toList

meta def keyOf (a : Array Nat) : Nat := [0, 1, 2, 3, 4].foldr (fun p acc => a[p]! + 100 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 100 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def kQ : List Nat := keyOrder gQ
meta def kC : List Nat := keyOrder gC

meta def comp (t u : Array Nat) : Array Nat := u.map fun i => t[i]!

meta def wits : Array (Array Nat) :=
  let pts := (CFSG.KC.BfsGen.search 100 7 gQ.toArray).1
  pts.map fun z =>
    #[((List.range 8).find? fun j =>
      let g := fyThrTab (j + 2)
      comp g fyThrX == comp z g).getD 0]

end CertificateChecks.KernelHS100.FyE

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS100.FT CFSG.EvenSporadicStandard.TwoHS.fyThrHex
#kmisc_hexflat CertificateChecks.KernelHS100.FT CFSG.EvenSporadicStandard.TwoHS.fyThrHex 3 100 7 13
#lc_bfs CertificateChecks.KernelHS100.FQ CertificateChecks.KernelHS100.FyE.gQ 100 7
#lc_bfs CertificateChecks.KernelHS100.FE CertificateChecks.KernelHS100.FyE.gC 100 7
#kss_natlist CertificateChecks.KernelHS100.FQ.SKT CertificateChecks.KernelHS100.FyE.kQ
#kss_natlist CertificateChecks.KernelHS100.FE.SKT CertificateChecks.KernelHS100.FyE.kC
#kmisc_packarrs CertificateChecks.KernelHS100.FW CertificateChecks.KernelHS100.FyE.wits 4

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] noncomputable def FQ.SK : List Nat := (List.range 9).map FQ.SKT

@[expose] noncomputable def FE.SK : List Nat := (List.range 36).map FE.SKT

@[expose] noncomputable def fyBr (k : Nat) : Bool :=
  CFSG.KC.Misc.ChainTail.ptailQ 100 7 HC.LR HC.TR (FT.F 0) 1 2 FE.N FE.T 2 2
    (pcomp 100 7 (mask 7) (pidn 100 7) (HC.TR (roff 100 (100 * 7) (HC.LR 1) + k)))

end CertificateChecks.KernelHS100

end
