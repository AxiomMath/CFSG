module

public import Certificates.Kernel.OmegaEight.E9KData
public import Certificates.Kernel.OmegaEight.AutChainAP
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityCheck
meta import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityCheck
meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local
meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pE9Local

namespace CertificateChecks.KernelO8.T3KE

open CFSG.HardMathSupport.Curtis.Coordinator CFSG.Monster.B.Co2.Native

meta def gR : List (Array Nat) := (triRGens triData).toList

meta def keyOf (a : Array Nat) : Nat := [1, 2].foldr (fun p acc => a[p]! + 360 * acc) 0

meta def kR : List Nat :=
  let pts := (CFSG.KC.BfsGen.search 360 9 gR.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def hL : List Nat := (triHArrs triData).toList.map (CFSG.KS.RawGen.pack 9)

meta def yL : List Nat := (triYArrs triData).toList.map (CFSG.KS.RawGen.pack 9)

meta def zL : List Nat := (triZArrs triData).toList.map (CFSG.KS.RawGen.pack 9)

meta def wL : List Nat :=
  let rp := (CFSG.KC.BfsGen.search 360 9 (triRGens triData)).1
  let hs := triHArrs triData
  let ys := triYArrs triData
  let zs := triZArrs triData
  rp.toList.map fun r =>
    ((List.range hs.size).find? fun e => triEntryOK hs[e]! ys[e]! zs[e]! r).getD 32

end CertificateChecks.KernelO8.T3KE

public section

set_option maxRecDepth 400000

#lc_bfs CertificateChecks.KernelO8.T3R CertificateChecks.KernelO8.T3KE.gR 360 9
#kss_natlist CertificateChecks.KernelO8.T3R.SKT CertificateChecks.KernelO8.T3KE.kR
#kss_natlist CertificateChecks.KernelO8.T3H CertificateChecks.KernelO8.T3KE.hL
#kss_natlist CertificateChecks.KernelO8.T3Y CertificateChecks.KernelO8.T3KE.yL
#kss_natlist CertificateChecks.KernelO8.T3Z CertificateChecks.KernelO8.T3KE.zL
#kss_natlist CertificateChecks.KernelO8.T3W CertificateChecks.KernelO8.T3KE.wL

namespace CertificateChecks.KernelO8.T3K

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelO8 CertificateChecks.KernelO8.E9K

@[expose] noncomputable def T3R.SK : List Nat := (List.range 729).map T3R.SKT

@[expose] def psR : List Nat := [1, 2]

@[expose] noncomputable def entK (e r : Nat) : Bool :=
  strictB (pm (T3H e) (pm r (pinvS 360 9 (mask 9) (T3H e)))) fun c =>
    Nat.beq (pm c (T3Y e)) (pm (T3Y e) c) && Nat.beq (pm c (T3Z e)) (pm (T3Z e) c)

@[expose] noncomputable def triK (i : Nat) : Bool :=
  !Nat.beq (pm (T3R.T i) (pm (T3R.T i) (T3R.T i))) (pidn 360 9) || memK 243 E9Q.T (T3R.T i) ||
    (Nat.blt (T3W i) 32 && entK (T3W i) (T3R.T i))

end CertificateChecks.KernelO8.T3K

end
