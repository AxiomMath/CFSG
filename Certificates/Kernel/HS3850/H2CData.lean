module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import Certificates.Data.HarrisLitN36HS2C
public meta import Certificates.Data.HarrisLitN36HS2C
public meta import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import Certificates.Kernel.SporSch.Mathieu.Gen

namespace CertificateChecks.KernelHS3850.H2CE

open CFSG.ComponentClassification.HarrisLit.N36.HS2C CFSG.Sporadic.SmallOddCore.Native
open CFSG.KS.SporSch.MOCG

meta def idM : Array Nat := idA 3850

meta def ids : Array (Array Nat) := #[idM, idM]

meta def gs7 : Array (Array Nat) := #[natArr y7, natArr x7]

meta def gs5 : Array (Array Nat) := #[natArr y5, natArr x5]

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

meta def sw7 : Array Nat := siftWord (natArr y7)

meta def sw5 : Array Nat := siftWord (natArr y5)

end CertificateChecks.KernelHS3850.H2CE

public section

set_option maxRecDepth 400000

#kmulh CertificateChecks.KernelHS3850.M7 3850 12 CertificateChecks.KernelHS3850.H2CE.ids
  CertificateChecks.KernelHS3850.H2CE.gs7 CertificateChecks.KernelHS3850.H2CE.idM 200
#kmulh CertificateChecks.KernelHS3850.M5 3850 12 CertificateChecks.KernelHS3850.H2CE.ids
  CertificateChecks.KernelHS3850.H2CE.gs5 CertificateChecks.KernelHS3850.H2CE.idM 400
#kss_list CertificateChecks.KernelHS3850.SW7 CertificateChecks.KernelHS3850.H2CE.sw7
#kss_list CertificateChecks.KernelHS3850.SW5 CertificateChecks.KernelHS3850.H2CE.sw5

end
