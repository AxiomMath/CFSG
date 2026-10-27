module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.LocalComp.BfsGenSl
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.HS100.ChainData
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.ChainTail
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5OutData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS100.S5OE

open CFSG.EvenSporadicStandard.HSStd

meta def gS : List (Array Nat) := s5oSGens.toList
meta def gE : List (Array Nat) := s5oCGens.toList
public meta def gC : List (Array Nat) := s5oXs.toList

public meta def keyOf (a : Array Nat) : Nat :=
  [0, 1, 2, 3, 4].foldr (fun p acc => a[p]! + 100 * acc) 0

public meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 100 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def kS : List Nat := keyOrder gS
meta def kE : List Nat := keyOrder gE
public meta def kC : List Nat := keyOrder gC

end CertificateChecks.KernelHS100.S5OE

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS100.OX CFSG.EvenSporadicStandard.HSStd.s5oHex
#kmisc_hexflat CertificateChecks.KernelHS100.OX CFSG.EvenSporadicStandard.HSStd.s5oHex 3 100 7 16
#lc_bfs CertificateChecks.KernelHS100.OS CertificateChecks.KernelHS100.S5OE.gS 100 7
#lc_bfs CertificateChecks.KernelHS100.OE CertificateChecks.KernelHS100.S5OE.gE 100 7
#kss_natlist CertificateChecks.KernelHS100.OS.SKT CertificateChecks.KernelHS100.S5OE.kS
#kss_natlist CertificateChecks.KernelHS100.OE.SKT CertificateChecks.KernelHS100.S5OE.kE

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

@[expose] noncomputable def OS.SK : List Nat := (List.range 1024).map OS.SKT

@[expose] noncomputable def OE.SK : List Nat := (List.range 1344).map OE.SKT

@[expose] noncomputable def rngK (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (100 * 7)) 0 && allN 100 (fun t => Nat.blt (pg 7 (mask 7) G t) 100)

@[expose] noncomputable def inHS (G : Nat) : Bool :=
  siftK 100 7 (mask 7) (100 * 7) (pidn 100 7) HC.LR HC.TRI HC.BP 5 0 G

@[expose] noncomputable def pm (p q : Nat) : Nat := pcomp 100 7 (mask 7) p q

@[expose] noncomputable def osOne (k : Nat) : Bool :=
  rngK (OS.T k) && (!inHS (OS.T k) || Nat.beq (pm (OX.F 4) (OS.T k)) (pm (OS.T k) (OX.F 4)))

@[expose] noncomputable def s5oBr (k : Nat) : Bool :=
  CFSG.KC.Misc.ChainTail.ptailK 100 7 HC.LR HC.TR HC.BP (OX.F 5) (fun _ => 0) [] OE.N OE.T 3 2
    (pcomp 100 7 (mask 7) (pidn 100 7) (HC.TR (roff 100 (100 * 7) (HC.LR 1) + k)))

end CertificateChecks.KernelHS100

end
