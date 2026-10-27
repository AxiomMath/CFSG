module

public import Certificates.Kernel.L34W.OutData
public import Certificates.Data.GrSLitL34Sec5SWFusCheck

public section

namespace CertificateChecks.KernelL34W

open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] def twoWit (kb : List Bool) : Array Nat :=
  let I := dedupKB kb (allM.filter (isInvKB kb))
  (I.findSome? fun x₁ => I.findSome? fun x₂ =>
    if !eqKB kb x₂ x₁ && commKB kb x₁ x₂ then
      let C := I.filter fun y => commKB kb y x₁ && commKB kb y x₂
      C.findSome? fun x₃ => C.findSome? fun x₄ =>
        if !commKB kb x₃ x₄ then some #[encM x₁, encM x₂, encM x₃, encM x₄] else none
    else none).getD #[0, 0, 0, 0]

@[expose] def twoArr : Array (Array Nat) := (kbMasks.map fun m => twoWit (kbOfMask m)).toArray

end CertificateChecks.KernelL34W

end
