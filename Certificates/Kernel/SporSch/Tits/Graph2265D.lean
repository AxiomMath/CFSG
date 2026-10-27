module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
meta import CFSG.Sporadic.Schreier.TitsGraphCheckInputs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelSporSch.TitsGraphD

open CFSG.Sporadic.Schreier.Tits

meta def pairs : List (Nat × Nat) := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

meta def nbM : Array Nat := (titsNbr.toList.map Array.toList).flatten.toArray

meta def nlM : Array Nat := (titsNbrLine.toList.map Array.toList).flatten.toArray

meta def pwM : Array Nat :=
  ((List.range 2925).flatMap fun v => pairs.map fun kk =>
    let a := titsLinePtArr[3 * v + kk.1]!
    let b := titsLinePtArr[3 * v + kk.2]!
    (titsNbr[a]!).idxOf b).toArray

meta def statesM : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := #[]
  for i in [0:7] do
    let mut s := initColor i
    out := out.push s
    for _ in [0:titsRounds[i]! + 1] do
      s := refineStep s
      out := out.push s
  return out

meta def sorted (col : Array Nat) (x : Nat) : List (Nat × Nat) :=
  ((titsNbr[x]!).toList.zipIdx.map fun (y, i) => (col[y]!, i)).mergeSort
    fun a b => decide (a.1 ≤ b.1)

meta def scM : Array (Array Nat) :=
  statesM.map fun col => ((List.range 1755).flatMap fun x => (sorted col x).map Prod.fst).toArray

meta def piM : Array (Array Nat) :=
  statesM.map fun col => ((List.range 1755).flatMap fun x => (sorted col x).map Prod.snd).toArray

meta def kM : Array Nat := statesM.map fun col => col.foldl (fun a c => max a (c + 1)) 0

meta def repM : Array (Array Nat) :=
  statesM.map fun col => (List.range (col.foldl (fun a c => max a (c + 1)) 0)).toArray.map
    fun c => col.idxOf c

end CertificateChecks.KernelSporSch.TitsGraphD

#ks_perm CertificateChecks.KernelSporSch.TitsGN.NB 11 CertificateChecks.KernelSporSch.TitsGraphD.nbM
#ks_perm CertificateChecks.KernelSporSch.TitsGN.NL 12 CertificateChecks.KernelSporSch.TitsGraphD.nlM
#ks_perm CertificateChecks.KernelSporSch.TitsGN.PW 4 CertificateChecks.KernelSporSch.TitsGraphD.pwM
#ks_perm CertificateChecks.KernelSporSch.TitsGS.K 11 CertificateChecks.KernelSporSch.TitsGraphD.kM
#kmisc_packarrs CertificateChecks.KernelSporSch.TitsGS.ST CertificateChecks.KernelSporSch.TitsGraphD.statesM 11
#kmisc_packarrs CertificateChecks.KernelSporSch.TitsGS.SC CertificateChecks.KernelSporSch.TitsGraphD.scM 11
#kmisc_packarrs CertificateChecks.KernelSporSch.TitsGS.PI CertificateChecks.KernelSporSch.TitsGraphD.piM 4
#kmisc_packarrs CertificateChecks.KernelSporSch.TitsGS.REP CertificateChecks.KernelSporSch.TitsGraphD.repM 11
