module

public import Certificates.Kernel.LocalComp.WittLev
public import Certificates.Kernel.LocalComp.WittData8165
public import Certificates.Data.Kernel.WittFix
public import CFSG.RankThree.PartTwo.KFacts.KP4Data
public import CFSG.RankThree.PartTwo.KFacts.KP4AutCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Witt

open CFSG.KC.WCnt CertificateChecks.KernelSpor.M22Syl CFSG.RankThree.PartTwo.KFacts.KP4

set_option maxRecDepth 100000

theorem k8164 : wc (fun f => (∀ p, f (ofTab deltaTab (ofTab (lineTab 0) p)) =
        ofTab (lineTab 0) (f (ofTab deltaTab p))) ∧
      ∀ p, f (ofTab deltaTab (ofTab (lineTab 1) p)) =
        ofTab (lineTab 1) (f (ofTab deltaTab p))) (pwp A B I wD) (fun x => Nat.beq x 0)
      (fun _ => inM 1097729) (fun _ _ => inM 2098433) = 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelLC.Witt

end
