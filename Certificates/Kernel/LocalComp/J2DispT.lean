module

public import Certificates.Kernel.LocalComp.J2Disp
public import CFSG.Certificates.Kernel.DecTextProved

public section

namespace CertificateChecks.KernelLC

open CFSG.KC.DecText CFSG.ComponentClassification.J2Cover.Models

theorem fRows_eq_proved : fRows = (natsK FR.chars).toArray :=
  FR.eq.trans (natsOf_ofList_proved kFR)

open Certificates in
open CFSG.ComponentClassification.J2Cover.Models in
theorem cert10026_proved :
    (bitAt fRows 2 16 && !bitAt fRows 16 2) = false ∧
      (!bitAt fRows 2 16 && bitAt fRows 16 2) = true := by
  rw [fRows_eq_proved]
  decide +kernel

end CertificateChecks.KernelLC

end
