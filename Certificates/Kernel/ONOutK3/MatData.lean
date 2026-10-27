module

public import CFSG.Certificates.Kernel.Enum.Defs
import Certificates.Kernel.SporSch.J4S.Gen
meta import Certificates.Data.GrSLitL34FactsCF23ONOutK3Data
meta import Certificates.Kernel.Sporadic.ON.Data
import Certificates.Kernel.Sporadic.ON.Data

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.F3.Native

meta def vPt (x : Nat) : V := (CertificateChecks.KernelSpor.ON.orbM.keys[x]!).toV

meta def ptRows (f : Nat → Nat) : Array V :=
  (Array.range 154).map fun t => vPt (f CFSG.ONSchreier.Data.spanIdx[t]!)

meta def piM : Array V := CFSG.Sporadic.ON.Native.invV 154 (ptRows fun x => x)

meta def matOf (a : Array Nat) : Array V := mul 154 piM (ptRows fun x => a[x]!)

meta def pack3 (X : Array V) : Nat := Id.run do
  let mut acc := 0
  for i in [0:154] do
    acc := acc ||| (X[i]!.p <<< (154 * i)) ||| (X[i]!.m <<< (23716 + 154 * i))
  return acc

meta def matLeaves : Array (Array Nat) :=
  let one := fun (a : Array Nat) => #[pack3 (matOf a)]
  #[#[pack3 piM]] ++ (Array.range 7).map (fun h => one CFSG.ONSchreier.qonStrongArrs[h]!) ++
    (Array.range 7).map (fun h => one CFSG.ONSchreier.qonInvArrs[h]!) ++
    (Array.range 7).map (fun h => one CFSG.ComponentClassification.SolMax.ONOut.sigStrong[h]!) ++
    (Array.range 7).map (fun h => one CFSG.ComponentClassification.SolMax.ONOut.sigStrongInv[h]!) ++
    (Array.range 3).map (fun a => one CFSG.ComponentClassification.SolMax.ONOut.hArrs[a]!)

end CertificateChecks.KernelSpor.ONK3

public section

#kss_tree CertificateChecks.KernelSpor.ONK3M CertificateChecks.KernelSpor.ONK3.matLeaves 47432

end
