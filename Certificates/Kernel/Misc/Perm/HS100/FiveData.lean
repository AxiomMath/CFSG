module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Kernel.Misc.Perm.ConjOrbCmd
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSFiveData
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSFiveData
meta import Certificates.Kernel.Sporadic.RawGen

public section

namespace CertificateChecks.KernelMisc.HS100.Five

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive
open CFSG.KC.BfsGen CFSG.KS.RawGen

meta def cuL : List (Array Nat) := cuGens.toList

meta def cfL : List (Array Nat) := cfGens.toList

meta def aL : List (Array Nat) := aGens.toList

meta def sL : List (Array Nat) := sGens.toList

meta def keyOf (a : Array Nat) : Nat := keys.foldr (fun p acc => a[p]! + 100 * acc) 0

meta def keyOrder (gs : List (Array Nat)) : List Nat :=
  let pts := (search 100 7 gs.toArray).1
  ((Array.range pts.size).qsort fun a b => keyOf pts[a]! < keyOf pts[b]!).toList

meta def cuKey : List Nat := keyOrder cuL

meta def cfKey : List Nat := keyOrder cfL

meta def aKey : List Nat := keyOrder aL

meta def sKey : List Nat := keyOrder sL

meta def powM (x : Array Nat) (e : Nat) : Array Nat :=
  (List.range e).foldl (fun acc _ => comp 100 x acc) (Array.range 100)

meta def w5 : Array (Array Nat) :=
  let pts := (search 100 7 cuGens).1
  pts.map fun x =>
    if powM x 5 == Array.range 100 && x != Array.range 100 then
      #[((List.range pts.size).find? fun j => comp 100 pts[j]! x == comp 100 f0 pts[j]!).getD 0]
    else #[0]

meta def wf : Array (Array Nat) :=
  let pts := (search 100 7 cfGens).1
  let as := (search 100 7 aGens).1
  pts.map fun x => Id.run do
    for e in [0:5] do
      for j in [0:as.size] do
        if x == comp 100 (powM f0 e) as[j]! then return #[e + 8 * j]
    return #[0]

meta def ws : Array (Array Nat) :=
  let pts := (search 100 7 sGens).1
  pts.map fun s =>
    #[((List.range conjs.size).find? fun c =>
      comp 100 conjs[c]! (comp 100 a3 (inv 100 conjs[c]!)) == s).getD 0]

meta def wt : Array (Array Nat) :=
  let as := (search 100 7 aGens).1
  let N := as.size
  let idx : Std.HashMap Nat Nat := (Array.range N).foldl (fun m i => m.insert (pack 7 as[i]!) i) {}
  as.map fun ak => Id.run do
    let mut rs : Array Nat := Array.replicate N 0
    if ak == Array.range 100 then return rs
    let cs := as.map fun aj => comp 100 aj (comp 100 ak (inv 100 aj))
    let mut seen : Array Bool := (Array.replicate N false).set! 0 true
    let mut q : Array Nat := #[0]
    let mut h := 0
    while h < q.size do
      let p := q[h]!
      for j in [0:N] do
        let y := comp 100 cs[j]! as[p]!
        let i := idx.getD (pack 7 y) 0
        if !seen[i]! then
          seen := seen.set! i true
          rs := rs.set! i (j + 64 * p + 4096 * (rs[p]! / 4096 + 1))
          q := q.push i
      h := h + 1
    return rs

end CertificateChecks.KernelMisc.HS100.Five

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMisc.HS100.Five.FX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.hexData
#kmisc_hexflat CertificateChecks.KernelMisc.HS100.Five.FX
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.hexData 3 100 7 21

#lc_bfs CertificateChecks.KernelMisc.HS100.Five.CU CertificateChecks.KernelMisc.HS100.Five.cuL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.Five.CF CertificateChecks.KernelMisc.HS100.Five.cfL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.Five.AA CertificateChecks.KernelMisc.HS100.Five.aL 100 7
#lc_bfs CertificateChecks.KernelMisc.HS100.Five.SS CertificateChecks.KernelMisc.HS100.Five.sL 100 7

#kss_natlist CertificateChecks.KernelMisc.HS100.Five.CUK CertificateChecks.KernelMisc.HS100.Five.cuKey
#kss_natlist CertificateChecks.KernelMisc.HS100.Five.CFK CertificateChecks.KernelMisc.HS100.Five.cfKey
#kss_natlist CertificateChecks.KernelMisc.HS100.Five.AAK CertificateChecks.KernelMisc.HS100.Five.aKey
#kss_natlist CertificateChecks.KernelMisc.HS100.Five.SSK CertificateChecks.KernelMisc.HS100.Five.sKey

#kmisc_packarrs CertificateChecks.KernelMisc.HS100.Five.W5 CertificateChecks.KernelMisc.HS100.Five.w5 32
#kmisc_packarrs CertificateChecks.KernelMisc.HS100.Five.WF CertificateChecks.KernelMisc.HS100.Five.wf 32
#kmisc_packarrs CertificateChecks.KernelMisc.HS100.Five.WS CertificateChecks.KernelMisc.HS100.Five.ws 32
#kmisc_packarrs CertificateChecks.KernelMisc.HS100.Five.WT CertificateChecks.KernelMisc.HS100.Five.wt 16

#conj_orb CertificateChecks.KernelMisc.HS100.Five.U
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.pGens 100 7
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.keys 700
  roots CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.u0 gens 2
