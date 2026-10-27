module

public import Certificates.Kernel.SporSch.HeT.Out2116
public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentCheckInputs

public section

namespace CertificateChecks.KernelSporSch.HeW17

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB

meta def wordsM : Array (List Int × Array (Array Nat)) :=
  #[(heCentW1, heLetterArrs), (heCentW2, heLetterArrs)] ++
    ((List.range 3).map fun j => (heDerivedV.getD j [], heCArrs)).toArray

meta def ncOf (wd : List Int) : Nat := max 1 ((wd.length + 5) / 6)

meta def ncM : Array Nat := wordsM.map fun p => ncOf p.1

meta def offM : Array Nat := (ncM.toList.foldl (fun (acc : Array Nat × Nat) c =>
  (acc.1.push acc.2, acc.2 + c)) (#[], 0)).1

meta def vsM : Array (Array Nat) := wordsM.toList.foldl (fun acc p =>
  acc ++ ((List.range (ncOf p.1)).map fun c =>
    wordA 8330 p.2 (p.2.map (invCand 8330)) (p.1.drop (6 * c))).toArray) #[]

meta def gjM : Array Nat :=
  ((List.range 5).flatMap fun j => List.replicate ncM[j]! j).toArray

meta def gcM : Array Nat :=
  ((List.range 5).flatMap fun j => List.range ncM[j]!).toArray

meta def uM : Array (Array Nat) := #[heUArr]

meta def invsM : Array (Array Nat) :=
  #[invCand 8330 heUArr, invCand 8330 heCArrs[0]!, invCand 8330 heCArrs[1]!]

meta def nfM : Array Nat := #[HeO16.nfOf heCArrs[0]!, HeO16.nfOf heCArrs[1]!]

end CertificateChecks.KernelSporSch.HeW17

#kss_perms CertificateChecks.KernelSporSch.HeW17V 14 CertificateChecks.KernelSporSch.HeW17.vsM

#kss_perms CertificateChecks.KernelSporSch.HeW17U 14 CertificateChecks.KernelSporSch.HeW17.uM

#kss_perms CertificateChecks.KernelSporSch.HeW17P 14 CertificateChecks.KernelSporSch.HeW17.invsM

#kss_list CertificateChecks.KernelSporSch.HeW17.NC CertificateChecks.KernelSporSch.HeW17.ncM

#kss_list CertificateChecks.KernelSporSch.HeW17.OFF CertificateChecks.KernelSporSch.HeW17.offM

#kss_list CertificateChecks.KernelSporSch.HeW17.GJ CertificateChecks.KernelSporSch.HeW17.gjM

#kss_list CertificateChecks.KernelSporSch.HeW17.GC CertificateChecks.KernelSporSch.HeW17.gcM

#kss_list CertificateChecks.KernelSporSch.HeW17.NF CertificateChecks.KernelSporSch.HeW17.nfM

#kss_list CertificateChecks.KernelSporSch.HeW17.FU CFSG.Sporadic.HeldB.heFixU

end
