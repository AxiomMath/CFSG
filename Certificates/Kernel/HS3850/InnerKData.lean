module

public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerData
public meta import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelHS3850.InnerE

open CFSG.KS.SporSch.MOCG CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

meta def c1 : Array (Array Nat) := hsC1Enum.tabs

meta def idM : Array Nat := idA 3850

meta def posC1 (t : Array Nat) : Nat := (c1.findIdx? (· == t)).getD c1.size

meta def mi : List Nat :=
  [tG, tA, tH, tY 0, tY 1, tY 2, tY 3, tCP 0, tCP 1, tCS 2, tCS 3].map posC1

meta def ow : List Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for c in [0:c1.size] do
    let x := c1[c]!
    let key := comp (comp (invA x) tG) x
    if !m.contains key then
      m := m.insert key c
  return (List.range c1.size).map fun i =>
    let t := c1[i]!
    if pow5 t == idM && t != idM then m.getD t 0 else 0

meta def fw : List Nat := (List.range c1.size).map fun i =>
  let y := c1[i]!
  if patOK y then
    (((List.range 20).flatMap fun k => (List.range 4).map fun j => (k, j)).find? fun p =>
      comp (hPow p.1) y == comp (tY p.2) (hPow p.1)).elim 0 fun p => 4 * p.1 + p.2
  else 0

meta def eGM : Array (Array Nat) := eGens tA

meta def eT : Array (Array Nat) := eEnum.tabs

meta def pw : List Nat := (List.range 8).map fun c =>
  let i := c / 4
  let j := c % 4
  let lhs := comp (tCP i) (wT (tY i) (eWc.getD j []))
  ((List.range eT.size).find? fun x => lhs == comp eT[x]! (tCP i)).getD 0

meta def letter (l : Nat) : Array Nat :=
  let S := CFSG.Sporadic.Schreier.hsStrongArrs
  if l < 8 then S[l]! else invA S[l - 8]!

meta def wval (w : List Nat) : Array Nat := w.foldr (fun l acc => comp (letter l) acc) (idA 3850)

meta def orbitWords (i : Nat) : Std.HashMap Nat (List Nat) := Id.run do
  let base := CFSG.Sporadic.Schreier.PairHS.baseArr
  let ls := (List.range 16).filter fun l => (List.range i).all fun m =>
    (letter l)[base[m]!]! == base[m]!
  let b := base[i]!
  let mut words : Std.HashMap Nat (List Nat) := (∅ : Std.HashMap Nat (List Nat)).insert b []
  let mut queue : Array Nat := #[b]
  let mut h := 0
  while h < queue.size do
    let q := queue[h]!
    h := h + 1
    let wq := words.getD q []
    for l in ls do
      let p := (letter l)[q]!
      if !words.contains p then
        words := words.insert p (l :: wq)
        queue := queue.push p
  return words

meta def siftWord (g : Array Nat) : Array Nat := Id.run do
  let base := CFSG.Sporadic.Schreier.PairHS.baseArr
  let mut h := g
  let mut out : List Nat := []
  for i in [0:4] do
    let p := h[base[i]!]!
    let u := (orbitWords i).getD p []
    out := out ++ u
    h := comp (invA (wval u)) h
  return out.toArray

meta def sw9 : Array Nat := siftWord (itab 9)
meta def sw10 : Array Nat := siftWord (itab 10)
meta def sw11 : Array Nat := siftWord (itab 11)

end CertificateChecks.KernelHS3850.InnerE

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelHS3850.IT
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert.innerHex
#kmisc_hexflat CertificateChecks.KernelHS3850.IT
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert.innerHex 3 3850 12 14
#kpenum_d CertificateChecks.KernelHS3850.EE 3850 12 false CertificateChecks.KernelHS3850.InnerE.eGM
  CertificateChecks.KernelHS3850.InnerE.eGM CertificateChecks.KernelHS3850.InnerE.idM 16
#kss_natlist CertificateChecks.KernelHS3850.MI CertificateChecks.KernelHS3850.InnerE.mi
#kss_natlist CertificateChecks.KernelHS3850.OW CertificateChecks.KernelHS3850.InnerE.ow
#kss_natlist CertificateChecks.KernelHS3850.FW CertificateChecks.KernelHS3850.InnerE.fw
#kss_natlist CertificateChecks.KernelHS3850.PW CertificateChecks.KernelHS3850.InnerE.pw
#kss_list CertificateChecks.KernelHS3850.SW9 CertificateChecks.KernelHS3850.InnerE.sw9
#kss_list CertificateChecks.KernelHS3850.SW10 CertificateChecks.KernelHS3850.InnerE.sw10
#kss_list CertificateChecks.KernelHS3850.SW11 CertificateChecks.KernelHS3850.InnerE.sw11

end
