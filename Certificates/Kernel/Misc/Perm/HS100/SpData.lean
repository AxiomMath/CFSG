module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialData
meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.Native.ChainCentralizer
meta import CFSG.RankThree.Native.ChainCentralizer

public section

namespace CertificateChecks.KernelMisc.HS100.Sp

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus CFSG.EvenSporadicStandard.HSStd
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def orb : CFSG.Monster.B.Fischer.ArrCert := zasFCert

meta def code (a : Array Nat) : Nat := (List.range 100).foldl (fun acc j => acc ||| (a[j]! <<< j)) 0

meta def oT : List Nat := orb.pts.toList.map code

meta def oE : List Nat := orb.edges.toList.map (pack 20)

meta def oD : List Nat := ((CFSG.KC.ConjOrbGen.treeOf orb.edges 2 0).getD #[]).toList

meta def oS : List Nat :=
  ((Array.range orb.pts.size).qsort fun a b => code orb.pts[a]! < code orb.pts[b]!).toList

meta def nW : List Nat :=
  let nP := (search 100 7 zasNGens).1
  let eP := (search 100 7 zasE0Gens).1
  (List.range eP.size).map fun i =>
    ((List.range nP.size).find? fun a =>
      comp 100 (comp 100 nP[a]! s5Z) (inv 100 nP[a]!) == eP[i]!).getD 0

end CertificateChecks.KernelMisc.HS100.Sp

end

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelMisc.HS100.Sp.OT CertificateChecks.KernelMisc.HS100.Sp.oT
#kss_natlist CertificateChecks.KernelMisc.HS100.Sp.OE CertificateChecks.KernelMisc.HS100.Sp.oE
#kss_natlist CertificateChecks.KernelMisc.HS100.Sp.OD CertificateChecks.KernelMisc.HS100.Sp.oD
#kss_natlist CertificateChecks.KernelMisc.HS100.Sp.OS CertificateChecks.KernelMisc.HS100.Sp.oS
#kss_natlist CertificateChecks.KernelMisc.HS100.Sp.NW CertificateChecks.KernelMisc.HS100.Sp.nW
