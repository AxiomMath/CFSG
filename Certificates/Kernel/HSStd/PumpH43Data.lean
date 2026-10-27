module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H43Data
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7H43Data
public import Std.Data.HashMap

public section

namespace CertificateChecks.KernelHSStd.PumpH43

open CFSG.EvenSporadicStandard.HSStd.PumpTC7 CFSG.KC.BfsGen CFSG.KS.RawGen
open CFSG.ComponentClassification.HarrisLit.P1 (Row)

meta def keyOf (a : Array Nat) : Nat := keys43.foldr (fun p acc => a[p]! + 80 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 80 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def rowM (j : Nat) : Option Row := rows43[j]?

meta def cgL (j : Nat) : List (Array Nat) :=
  match rowM j with
  | some r => (cgArr r).toList
  | none => []

meta def cgP (j : Nat) : List Nat := (cgL j).map (pack 7)

meta def dL (j : Nat) : List (Array Nat) :=
  match rowM j with
  | some r => match derPairs.find? (fun p => p.1 == r.row.rep) with
    | some p => (derComms r p.2).toList
    | none => []
  | none => []

meta def cg0 : List Nat := cgP 0
meta def cg3 : List Nat := cgP 3
meta def cg9 : List Nat := cgP 9
meta def d0L : List (Array Nat) := dL 0
meta def d3L : List (Array Nat) := dL 3
meta def d9L : List (Array Nat) := dL 9
meta def c10L : List (Array Nat) := cgL 10

meta def d0Key : List Nat := keyOrder d0L
meta def d3Key : List Nat := keyOrder d3L
meta def d9Key : List Nat := keyOrder d9L
meta def c10Key : List Nat := keyOrder c10L

meta def x0M : Array Nat :=
  ((search 80 7 c10L.toArray).1.toList.filter isOrd3).headD (Array.range 80)

meta def i0M : List Nat :=
  let cs := (search 80 7 c10L.toArray).1
  [((List.range cs.size).find? fun i => isOrd3 cs[i]!).getD 0]

meta def qWit : List Nat :=
  let cs := (search 80 7 c10L.toArray).1
  let qs := (CFSG.KC.ConjOrbGen.search 80 7 gsP x0M).1
  let idx : Std.HashMap (Array Nat) Nat := (Array.range qs.size).foldl (fun m i => m.insert qs[i]! i) {}
  (cs.map fun a => if isOrd3 a then idx.getD a 0 else 0).toList

end CertificateChecks.KernelHSStd.PumpH43

end

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelHSStd.PumpH43.CG0 CertificateChecks.KernelHSStd.PumpH43.cg0
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.CG3 CertificateChecks.KernelHSStd.PumpH43.cg3
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.CG9 CertificateChecks.KernelHSStd.PumpH43.cg9

#lc_bfs CertificateChecks.KernelHSStd.PumpH43.D0 CertificateChecks.KernelHSStd.PumpH43.d0L 80 7
#lc_bfs CertificateChecks.KernelHSStd.PumpH43.D3 CertificateChecks.KernelHSStd.PumpH43.d3L 80 7
#lc_bfs CertificateChecks.KernelHSStd.PumpH43.D9 CertificateChecks.KernelHSStd.PumpH43.d9L 80 7
#lc_bfs CertificateChecks.KernelHSStd.PumpH43.C10 CertificateChecks.KernelHSStd.PumpH43.c10L 80 7

#kss_natlist CertificateChecks.KernelHSStd.PumpH43.D0K CertificateChecks.KernelHSStd.PumpH43.d0Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.D3K CertificateChecks.KernelHSStd.PumpH43.d3Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.D9K CertificateChecks.KernelHSStd.PumpH43.d9Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.C10K CertificateChecks.KernelHSStd.PumpH43.c10Key
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.QW CertificateChecks.KernelHSStd.PumpH43.qWit
#kss_natlist CertificateChecks.KernelHSStd.PumpH43.I0 CertificateChecks.KernelHSStd.PumpH43.i0M

#conj_orb CertificateChecks.KernelHSStd.PumpH43.Q CFSG.EvenSporadicStandard.HSStd.PumpTC7.gsP 80 7
  CFSG.EvenSporadicStandard.HSStd.PumpTC7.keys43 1440
  roots CertificateChecks.KernelHSStd.PumpH43.x0M gens 2
