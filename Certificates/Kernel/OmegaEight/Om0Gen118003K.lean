module

public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Data.Om0GenCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

@[expose] def om0VW : List Int :=
  CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0 CFSG.ClassicalInvolution.Q3.TL4.E4O8Data.v0Word

@[expose] noncomputable def om0V : Nat := wO om0VW

theorem kOm0 : bAnd(allN 8 (fun i => bAnd(pm (AP.S i), cn (pinv (AP.S i)))),
    bAnd(lettersK 17 om0VW, bAnd(cn om0V,
    bAnd(List.all [0, 1, 2, 4, 5, 6, 7]
      (fun l => Nat.beq (pc (AP.S l) (mainK 0)) (pc (mainK 0) (AP.S l))),
    Nat.beq (cj (AP.S 3) (mainK 0))
      (pc (pc (pc (cj (AP.S 0) om0V) (cj (AP.S 2) om0V)) (cj (AP.S 4) om0V))
        (cj (AP.S 6) (pc om0V (mainK 0)))))))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
