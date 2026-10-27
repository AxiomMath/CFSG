module

public import Certificates.Kernel.SporSch.HeT.X2114
public import Certificates.Kernel.Sporadic.He.Bind2112
public import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.HeldB.InnerCheckInputs

public section

namespace CertificateChecks.KernelSporSch.HeB14

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB

meta def wordsM : Array (List Int × Array (Array Nat)) :=
  ((List.range 9).map fun j => (heInnerWords0.getD j [], heInnerLetters0)).toArray ++
    ((List.range 9).map fun j => (heInnerWords1.getD j [], heInnerLetters1)).toArray ++
    #[(heT1Word, heABArrs)]

meta def ncOf (wd : List Int) : Nat := max 1 ((wd.length + 5) / 6)

meta def ncM : Array Nat := wordsM.map fun p => ncOf p.1

meta def offM : Array Nat := (ncM.toList.foldl (fun (acc : Array Nat × Nat) c =>
  (acc.1.push acc.2, acc.2 + c)) (#[], 0)).1

meta def vsM : Array (Array Nat) := wordsM.toList.foldl (fun acc p =>
  acc ++ ((List.range (ncOf p.1)).map fun c =>
    wordA 8330 p.2 (p.2.map (invCand 8330)) (p.1.drop (6 * c))).toArray) #[]

meta def gjM : Array Nat :=
  ((List.range 19).flatMap fun j => List.replicate ncM[j]! j).toArray

meta def gcM : Array Nat :=
  ((List.range 19).flatMap fun j => List.range ncM[j]!).toArray

meta def invsM : Array (Array Nat) :=
  #[invCand 8330 heT1Arr] ++
    ((List.range 9).map fun j => invCand 8330 (heInnerC0 j)).toArray ++
    ((List.range 9).map fun j => invCand 8330 (heInnerC1 j)).toArray

end CertificateChecks.KernelSporSch.HeB14

#kss_perms CertificateChecks.KernelSporSch.HeB14V 14 CertificateChecks.KernelSporSch.HeB14.vsM

#kss_perms CertificateChecks.KernelSporSch.HeB14P 14 CertificateChecks.KernelSporSch.HeB14.invsM

#kss_list CertificateChecks.KernelSporSch.HeB14.NC CertificateChecks.KernelSporSch.HeB14.ncM

#kss_list CertificateChecks.KernelSporSch.HeB14.OFF CertificateChecks.KernelSporSch.HeB14.offM

#kss_list CertificateChecks.KernelSporSch.HeB14.GJ CertificateChecks.KernelSporSch.HeB14.gjM

#kss_list CertificateChecks.KernelSporSch.HeB14.GC CertificateChecks.KernelSporSch.HeB14.gcM

#kss_list CertificateChecks.KernelSporSch.HeB14.D0 CFSG.Sporadic.HeldB.heDelta0

#kss_list CertificateChecks.KernelSporSch.HeB14.D1 CFSG.Sporadic.HeldB.heDelta1

end
