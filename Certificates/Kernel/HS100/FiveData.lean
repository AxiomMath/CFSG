module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.RankThree.Native.HSMcLFiveData
meta import CFSG.RankThree.Native.HSMcLFiveData
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.HSMcLSmallData
meta import CFSG.RankThree.Native.HSMcLSmallData

namespace CertificateChecks.KernelHS100.FiveE

meta def c0 : List (Array Nat) := CFSG.RankThree.Native.hs100FiveC0Gens.toList

meta def c2 : List (Array Nat) := CFSG.RankThree.Native.hs100FiveC2Gens.toList

meta def c23 : List (Array Nat) := CFSG.RankThree.Native.hs100FiveC23Gens.toList

public meta def keyOf (a : Array Nat) : Nat :=
  [0, 1, 3, 2, 4, 5].foldr (fun p acc => a[p]! + 100 * acc) 0

public meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 100 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def k0 : List Nat := keyOrder c0

meta def k2 : List Nat := keyOrder c2

meta def k23 : List Nat := keyOrder c23

end CertificateChecks.KernelHS100.FiveE

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS100.FV CFSG.RankThree.Native.hs100FiveHex
#kmisc_hexflat CertificateChecks.KernelHS100.FV CFSG.RankThree.Native.hs100FiveHex 3 100 7 82

#lc_bfs CertificateChecks.KernelHS100.C0 CertificateChecks.KernelHS100.FiveE.c0 100 7
#lc_bfs CertificateChecks.KernelHS100.C2 CertificateChecks.KernelHS100.FiveE.c2 100 7
#lc_bfs CertificateChecks.KernelHS100.C23 CertificateChecks.KernelHS100.FiveE.c23 100 7
#kss_natlist CertificateChecks.KernelHS100.C0.SKT CertificateChecks.KernelHS100.FiveE.k0
#kss_natlist CertificateChecks.KernelHS100.C2.SKT CertificateChecks.KernelHS100.FiveE.k2
#kss_natlist CertificateChecks.KernelHS100.C23.SKT CertificateChecks.KernelHS100.FiveE.k23

namespace CertificateChecks.KernelHS100

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin

@[expose] noncomputable def C0.SK : List Nat := (List.range 50).map C0.SKT

@[expose] noncomputable def C2.SK : List Nat := (List.range 600).map C2.SKT

@[expose] noncomputable def C23.SK : List Nat := (List.range 1000).map C23.SKT

theorem C0.keys : keysSK 100 7 [0, 1, 3, 2, 4, 5] C0.N C0.T C0.SK = true := by quickRfl

theorem C2.keys : keysSK 100 7 [0, 1, 3, 2, 4, 5] C2.N C2.T C2.SK = true := by quickRfl

theorem C23.keys : keysSK 100 7 [0, 1, 3, 2, 4, 5] C23.N C23.T C23.SK = true := by quickRfl

theorem permF : allN 82
    (fun j => permOK 100 7 (mask 7) (100 * 7) (FV.F j) (pinvS 100 7 (mask 7) (FV.F j))) = true := by
  quickRfl

theorem gensF : (allN 3 fun k => Nat.beq (C0.G k) (FV.F (64 + k))) = true ∧
    (allN 4 fun k => Nat.beq (C2.G k) (FV.F (67 + k))) = true ∧
    (allN 4 fun k => Nat.beq (C23.G k) (FV.F (71 + k))) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelHS100

end
