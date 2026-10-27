module

public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporSuzInputs
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzPair

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0
  CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.LocalR CFSG.LocalAnalysis.WeakClosure81.SporSuz

meta def sT : Array (Array Nat) := (enumBFS 1782 s1Gens 8192).tabs

meta def diffAt (x y : Array Nat) : Nat :=
  ((List.range 1782).find? fun p => !(x[p]! == y[p]!)).map (· + 1) |>.getD 0

meta def zCode (x : Array Nat) : Nat :=
  match (List.range 4).find? (fun j => !(commT x s1Gens[j]!)) with
  | none => 0
  | some j => 2048 * j + diffAt (comp 1782 x s1Gens[j]!) (comp 1782 s1Gens[j]! x)

meta def z2Code (x : Array Nat) : Nat :=
  match (List.range 4).find? (fun j => !(commT x s1Gens[j]! || commZT x s1Gens[j]!)) with
  | none => 0
  | some j =>
    let y := s1Gens[j]!
    1 + 4194304 * j + 2048 * (diffAt (comp 1782 x y) (comp 1782 y x) - 1) +
      (diffAt (comp 1782 x y) (comp 1782 tTab (comp 1782 y x)) - 1)

meta def rowsOf (a : Array Nat) : Array (Array Nat) :=
  (List.range ((a.size + 31) / 32)).toArray.map fun r =>
    (List.range 32).toArray.map fun t => a.getD (32 * r + t) 0

meta def wZR : Array (Array Nat) := rowsOf (sT.map zCode)
meta def w2R : Array (Array Nat) := rowsOf (sT.map z2Code)

meta def tabsL : Array (Array Nat) :=
  #[invTab 1782 b0Arr, invTab 1782 b1Arr, invTab 1782 (cTab 2), invTab 1782 (cTab 4), gTab (),
    invTab 1782 (gTab ())]

end CertificateChecks.KernelSpor.SuzPair

public section

#kmisc_packarrs CertificateChecks.KernelSpor.SuzPairWZ CertificateChecks.KernelSpor.SuzPair.wZR 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzPairW2 CertificateChecks.KernelSpor.SuzPair.w2R 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzPairT CertificateChecks.KernelSpor.SuzPair.tabsL 11

end
