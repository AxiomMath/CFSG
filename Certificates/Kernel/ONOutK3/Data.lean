module

public import CFSG.Certificates.Kernel.Enum.Defs
import Certificates.Kernel.SporSch.J4S.Gen
meta import Certificates.Data.GrSLitL34FactsCF23ONOutK3Data

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.ComponentClassification.SolMax.ONOut

meta def chunks (xs : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := (xs.size + 63) / 64) fun i => xs.extract (64 * i.val) (64 * i.val + 64)

meta def key3 (t : Nat × Nat × Nat) : Nat := t.1 ||| (t.2.1 <<< 18) ||| (t.2.2 <<< 36)

meta def nodeRecs : Array Nat := Id.run do
  let (par, lab, im) := mTree
  let pm := posMap3 im
  let sim := mSim
  let n := im.size
  let mut dep : Array Nat := Array.replicate n 0
  let mut wrd : Array Nat := Array.replicate n 0
  for k in [1:n] do
    let q := par[k]!
    dep := dep.set! k (dep[q]! + 1)
    wrd := wrd.set! k (wrd[q]! + (lab[k]! <<< (2 * dep[q]!)))
  let mut out : Array Nat := Array.mkEmpty n
  for k in [0:n] do
    let t := im[k]!
    let p0 := pm.getD (arrStep hArrs 0 t) n
    let p1 := pm.getD (arrStep hArrs 1 t) n
    let p2 := pm.getD (arrStep hArrs 2 t) n
    out := out.push (key3 t ||| (p0 <<< 54) ||| (p1 <<< 72) ||| (p2 <<< 90) ||| (par[k]! <<< 108) |||
      (lab[k]! <<< 126) ||| (pm.getD sim[k]! n <<< 128) ||| (dep[k]! <<< 146) ||| (wrd[k]! <<< 151))
  return out

meta def nodeLeaves : Array (Array Nat) := chunks nodeRecs

meta def sortLeaves : Array (Array Nat) :=
  let im := mIm
  let ks := (Array.range im.size).map fun k => (key3 im[k]!, k)
  let s := ks.qsort fun a b => a.1 < b.1
  chunks (s.map fun p => p.1 ||| (p.2 <<< 54))

meta def countLeaves : Array (Array Nat) :=
  chunks (Array.ofFn (n := 315) fun s =>
    ((List.range 512).filter fun l => tTest (512 * s.val + l)).length)

meta def fLeaves : Array (Array Nat) :=
  let (par, lab, im) := fTree
  let pm := posMap3 im
  #[(Array.range 60).map fun k =>
    key3 im[k]! ||| (pm.getD (fStep 0 im[k]!) 60 <<< 54) ||| (pm.getD (fStep 1 im[k]!) 60 <<< 60) |||
      (par[k]! <<< 66) ||| (lab[k]! <<< 72)]

meta def keyLeaves : Array (Array Nat) := #[(fIm ++ zfIm).map key3]

end CertificateChecks.KernelSpor.ONK3

public section

#kss_tree CertificateChecks.KernelSpor.ONK3N CertificateChecks.KernelSpor.ONK3.nodeLeaves 193
#kss_tree CertificateChecks.KernelSpor.ONK3S CertificateChecks.KernelSpor.ONK3.sortLeaves 72
#kss_tree CertificateChecks.KernelSpor.ONK3C CertificateChecks.KernelSpor.ONK3.countLeaves 10
#kss_tree CertificateChecks.KernelSpor.ONK3F CertificateChecks.KernelSpor.ONK3.fLeaves 73
#kss_tree CertificateChecks.KernelSpor.ONK3K CertificateChecks.KernelSpor.ONK3.keyLeaves 54

end
