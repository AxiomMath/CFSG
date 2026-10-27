module

public import Certificates.Kernel.L34W.OutData

public section

namespace CertificateChecks.KernelL34W

open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

@[expose] def d1Row (m n : Nat) (c : Array Nat) : Array Nat :=
  let kb := kbOfMask m
  let F := fixInvs kb (n % 64) (n / 64)
  (Array.range 144).flatMap fun j' =>
    if c.getD j' 0 == 1 then
      let n' := outCodes.getD j' 0
      let D := dedupKB kb (F.filter fun x => fixKB kb (n' % 64) (n' / 64) x)
      #[encM (D.getD 0 oneM), encM (D.getD 1 oneM)]
    else #[0, 0]

@[expose] def d1Arr : Array (Array Nat) :=
  (Array.range 14).flatMap fun q =>
    (Array.range 144).map fun j => d1Row (kbMasks.getD q 0) (outCodes.getD j 0) (cmArr.getD j #[])

end CertificateChecks.KernelL34W

end
