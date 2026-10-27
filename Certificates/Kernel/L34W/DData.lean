module

public import Certificates.Kernel.L34W.OutData

public section

namespace CertificateChecks.KernelL34W

open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] def lfArr : Array (Array Nat) :=
  (Array.range 15).map fun q =>
    (Array.range 36).map fun i => if liftsKB (kbOfMask (kbMasks.getD q 0)) i then 1 else 0

@[expose] def tyArr : Array (Array Nat) := outCodes.map fun n => #[typeOf (n % 64) (n / 64)]

@[expose] def dCell (kb : List Bool) (F : List MElt) (k : Nat) : Array Nat :=
  let I := F.filter fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)
  match I.find? (fun x => x.1 != 0 && x.1 != k) with
  | some x => #[0, encM x, 0, 0, 0]
  | none =>
    let D := dedupKB kb I
    let e := fun l => encM (D.getD l oneM)
    if 4 ≤ D.length then #[1, e 0, e 1, e 2, e 3] else #[2, e 0, e 1, e 2, 0]

@[expose] def dRow (m n : Nat) : Array Nat :=
  let kb := kbOfMask m
  if liftsKB kb (n / 64) then
    let F := fixInvs kb (n % 64) (n / 64)
    let K := kVals (n % 64) (n / 64)
    (Array.range 64).flatMap fun k => if K.contains k then dCell kb F k else #[0, 0, 0, 0, 0]
  else #[]

@[expose] def dArr : Array (Array Nat) :=
  (Array.range 15).flatMap fun q => outCodes.map fun n => dRow (kbMasks.getD q 0) n

end CertificateChecks.KernelL34W

end
