module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H39Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H39Data

public section

namespace CertificateChecks.KernelHSStd.PumpH39

open CFSG.EvenSporadicStandard.HSStd.PumpTC7 CFSG.KC.BfsGen
open CFSG.EvenSmallLie.Child3.SelL39 (tW)

meta def keyOf (a : Array Nat) : Nat := tKeys.foldr (fun p acc => a[p]! + 182 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 182 8 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def s2L : List (Array Nat) := s2Gens.toList

meta def wsM (j : Nat) : List (List Int) := ((exclTab.getD j none).map (·.1)).getD []

meta def eL (j : Nat) : List (Array Nat) := (wsM j).map tW

meta def e0L : List (Array Nat) := eL 0
meta def e1L : List (Array Nat) := eL 1
meta def e3L : List (Array Nat) := eL 3
meta def e5L : List (Array Nat) := eL 5
meta def e7L : List (Array Nat) := eL 7
meta def e9L : List (Array Nat) := eL 9
meta def e10L : List (Array Nat) := eL 10

meta def s2Key : List Nat := keyOrder s2L
meta def e0Key : List Nat := keyOrder e0L
meta def e1Key : List Nat := keyOrder e1L
meta def e3Key : List Nat := keyOrder e3L
meta def e5Key : List Nat := keyOrder e5L
meta def e7Key : List Nat := keyOrder e7L
meta def e9Key : List Nat := keyOrder e9L
meta def e10Key : List Nat := keyOrder e10L

meta def xWit : List Nat :=
  let us := (search 182 8 uGens).1
  let xs := (CFSG.KC.ConjOrbGen.search 182 8 gsT x1).1
  let idx : Std.HashMap (Array Nat) Nat := (Array.range xs.size).foldl (fun m i => m.insert xs[i]! i) {}
  (us.map fun a =>
    if ((List.range 182).filter fun p => a[p]! == p).length == 20 then idx.getD a 0 else 0).toList

end CertificateChecks.KernelHSStd.PumpH39

end

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelHSStd.PumpH39.S2 CertificateChecks.KernelHSStd.PumpH39.s2L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E0 CertificateChecks.KernelHSStd.PumpH39.e0L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E1 CertificateChecks.KernelHSStd.PumpH39.e1L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E3 CertificateChecks.KernelHSStd.PumpH39.e3L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E5 CertificateChecks.KernelHSStd.PumpH39.e5L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E7 CertificateChecks.KernelHSStd.PumpH39.e7L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E9 CertificateChecks.KernelHSStd.PumpH39.e9L 182 8
#lc_bfs CertificateChecks.KernelHSStd.PumpH39.E10 CertificateChecks.KernelHSStd.PumpH39.e10L 182 8

#kss_natlist CertificateChecks.KernelHSStd.PumpH39.S2K CertificateChecks.KernelHSStd.PumpH39.s2Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E0K CertificateChecks.KernelHSStd.PumpH39.e0Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E1K CertificateChecks.KernelHSStd.PumpH39.e1Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E3K CertificateChecks.KernelHSStd.PumpH39.e3Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E5K CertificateChecks.KernelHSStd.PumpH39.e5Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E7K CertificateChecks.KernelHSStd.PumpH39.e7Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E9K CertificateChecks.KernelHSStd.PumpH39.e9Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.E10K CertificateChecks.KernelHSStd.PumpH39.e10Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH39.XW CertificateChecks.KernelHSStd.PumpH39.xWit

#conj_orb CertificateChecks.KernelHSStd.PumpH39.X CFSG.EvenSporadicStandard.HSStd.PumpTC7.gsT 182 8
  CFSG.EvenSporadicStandard.HSStd.PumpTC7.tKeys 728
  roots CFSG.EvenSporadicStandard.HSStd.PumpTC7.x1 gens 2
