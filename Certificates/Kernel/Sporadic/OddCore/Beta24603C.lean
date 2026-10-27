module

public import Certificates.Kernel.Sporadic.OddCore.Beta24603D
public import Certificates.Data.Kernel.Spor.ColH
public import CFSG.Certificates.Kernel.Common.Benes
meta import Certificates.Kernel.Sporadic.OddCore.Beta24603D
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaCheck

public section

namespace CertificateChecks.KernelSpor.B24603

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native

meta def colM : Array (Array Nat) :=
  (Array.range 6156).map fun i => recM.map fun e => e[i]!

meta def idxM : Std.HashMap (Array Nat) Nat := Id.run do
  let mut idx : Std.HashMap (Array Nat) Nat := {}
  for j in [0:recM.size] do
    idx := idx.insert recM[j]! j
  return idx

meta def piM (l : Nat) : Array Nat := Id.run do
  let g := gM[l]!
  let mut r : Array Nat := Array.range 2048
  for j in [0:recM.size] do
    let e := recM[j]!
    r := r.set! j (idxM.getD (Array.ofFn (n := 6156) fun i => e[g[i.val]!]!) 4095)
  return r

meta def piInvM : Array (Array Nat) := (Array.range 2).map fun l => Id.run do
  let p := piM l
  let mut r : Array Nat := Array.replicate 2048 0
  for j in [0:2048] do
    r := r.set! p[j]! j
  return r

meta def fnvM (a : Array Nat) : Nat :=
  a.foldl (fun h v => ((h ^^^ v) * 1099511628211) % 18446744073709551616) 14695981039346656037

meta def hashM : Array (Array Nat) :=
  (Array.range 8).map fun r => (Array.range 135).map fun m => fnvM recM[8 * m + r]!

meta def hsM : Array (Array Nat) :=
  let h := recM.map fnvM
  let hs := (Array.range 1080).qsort fun a b => h[a]! < h[b]!
  let inv := Id.run do
    let mut r : Array Nat := Array.replicate 1080 0
    for i in [0:1080] do
      r := r.set! hs[i]! i
    return r
  #[hs, inv]

meta def treeM : Array (Array Nat) :=
  let p0 := piM 0
  let p1 := piM 1
  #[bfsM.par, bfsM.lab, (Array.range 2160).map fun c => if c % 2 == 0 then p0[c / 2]! else p1[c / 2]!]

meta def bkM : Array (Array Nat) :=
  let b := natArr (j3BetaTbl 7)
  #[#[idxM.getD b 4095, idxM.getD (Array.ofFn (n := 6156) fun i => b[b[i.val]!]!) 4095]]

end CertificateChecks.KernelSpor.B24603

#kmisc_packarrs CertificateChecks.KernelSpor.B24603Col CertificateChecks.KernelSpor.B24603.colM 16

#kmisc_packarrs CertificateChecks.KernelSpor.B24603Pi CertificateChecks.KernelSpor.B24603.piInvM 16

#kmisc_packarrs CertificateChecks.KernelSpor.B24603Hx CertificateChecks.KernelSpor.B24603.hashM 128

#kmisc_packarrs CertificateChecks.KernelSpor.B24603Hs CertificateChecks.KernelSpor.B24603.hsM 16

#kmisc_packarrs CertificateChecks.KernelSpor.B24603Bk CertificateChecks.KernelSpor.B24603.bkM 16

#kmisc_packarrs CertificateChecks.KernelSpor.B24603Tr CertificateChecks.KernelSpor.B24603.treeM 16

#kc_benes CertificateChecks.KernelSpor B24603N 0 2 15 fun _ j =>
  CFSG.KS.ColH.expP 11 (CertificateChecks.KernelSpor.B24603Pi j)

end
