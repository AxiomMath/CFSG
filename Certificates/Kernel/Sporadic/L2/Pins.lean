module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
meta import CFSG.Sporadic.SuzRecog.LevelTwoCheck
public import Mathlib
meta import Mathlib

public section

namespace CertificateChecks.KernelSpor.L2Pins

open CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Monster.B.Co2.Native

meta def aPin : Array (Array Nat) := aPts

meta def tPin : Array (Array Nat) := (Array.range 486).map fun i => (trip (i / 3))[i % 3]!

meta def vPin : Array (Array Nat) := #[vtab 0, vtab 1]

meta def eiPin : Array (Array Nat) := (Array.range 21).map fun k => (eltPin k).2

meta def ordOf (f : Array Nat) : Array Nat := (Array.range f.size).qsort fun a b => f[a]! < f[b]!

meta def posOf (f : Array Nat) : Array Nat := Id.run do
  let o := ordOf f
  let mut p : Array Nat := Array.replicate f.size 0
  for m in [0:o.size] do
    p := p.set! o[m]! m
  return p

meta def fA : Array Nat := aPts.map fp

meta def fT : Array Nat := tPin.map fp

meta def oaPin : Array (Array Nat) := #[ordOf fA]

meta def paPin : Array (Array Nat) := #[posOf fA]

meta def otPin : Array (Array Nat) := #[ordOf fT]

meta def ptPin : Array (Array Nat) := #[posOf fT]

end CertificateChecks.KernelSpor.L2Pins

#kmisc_packarrs CertificateChecks.KernelSpor.L2A CertificateChecks.KernelSpor.L2Pins.aPin 11
#kmisc_packarrs CertificateChecks.KernelSpor.L2T CertificateChecks.KernelSpor.L2Pins.tPin 11
#kmisc_packarrs CertificateChecks.KernelSpor.L2V CertificateChecks.KernelSpor.L2Pins.vPin 12
#kmisc_packarrs CertificateChecks.KernelSpor.L2EI CertificateChecks.KernelSpor.L2Pins.eiPin 11
#kmisc_packarrs CertificateChecks.KernelSpor.L2OA CertificateChecks.KernelSpor.L2Pins.oaPin 12
#kmisc_packarrs CertificateChecks.KernelSpor.L2PA CertificateChecks.KernelSpor.L2Pins.paPin 12
#kmisc_packarrs CertificateChecks.KernelSpor.L2OT CertificateChecks.KernelSpor.L2Pins.otPin 12
#kmisc_packarrs CertificateChecks.KernelSpor.L2PT CertificateChecks.KernelSpor.L2Pins.ptPin 12

end
