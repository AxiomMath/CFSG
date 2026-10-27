module

public import Certificates.Kernel.SporSch.Ru.GensData
public import Certificates.Kernel.SporSch.Ru.WordsGen
public import Certificates.Data.CFSGNative.Bridge.SurjD
meta import Certificates.Data.CFSGNative.Bridge.SurjD
meta import CFSG.Sporadic.Schreier.RuArrays
meta import CFSG.Sporadic.Schreier.RuEnum
meta import Mathlib.GroupTheory.Schreier

public section

namespace CertificateChecks.KernelSporSch.RuPD

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Sporadic.Bridge.SurjD.Native

meta def baseM : Array (Array Nat) := #[ruA0A, ruInv ruA0A, ruA1A, ruInv ruA1A]

meta def uM : Array (Array Nat) := (parseWords ruImgText).map fun w =>
  w.foldr (fun z T => compA 4060 baseM[z.toNat]! T) (idA 4060)

meta def uiM : Array (Array Nat) := uM.map ruInv

meta def toPair (z : Int) : Nat × Bool := if 0 < z then ((z - 1).toNat, true) else ((-z - 1).toNat, false)

meta def wsM : List (List (Nat × Bool)) :=
  ruRels () ++ ((parseWords ruSurjText).toList.map fun w => w.map toPair)

meta def valM (v : List (Nat × Bool)) : Array Nat :=
  v.foldr (fun l T => compA 4060 (if l.2 then uM[l.1]! else uiM[l.1]!) T) (idA 4060)

meta def ttM : Array (Array Nat) := (Array.range (16 * 14)).map fun j =>
  valM ((wsM.getD (j / 16) []).drop (20 * (j % 16)))

end CertificateChecks.KernelSporSch.RuPD

#kss_perms CertificateChecks.KernelSporSch.RuPD.U 12 CertificateChecks.KernelSporSch.RuPD.uM
#kss_perms CertificateChecks.KernelSporSch.RuPD.UI 12 CertificateChecks.KernelSporSch.RuPD.uiM
#kss_perms CertificateChecks.KernelSporSch.RuPD.TT 12 CertificateChecks.KernelSporSch.RuPD.ttM
#kss_words CertificateChecks.KernelSporSch.RuPD.WS CertificateChecks.KernelSporSch.RuPD.wsM

end
