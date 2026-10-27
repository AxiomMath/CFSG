module

public import CFSG.Certificates.Kernel.DecTextSound
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverExclusion
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferCocycle
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsTables
meta import Certificates.Kernel.LocalComp.NatsGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations.QuasisimpleMulEquiv
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import Certificates.Kernel.LocalComp.NatsGen

public section

#lc_natsof CertificateChecks.KernelLC.FR CFSG.ComponentClassification.J2Cover.Models.fRows

namespace CertificateChecks.KernelLC

open CFSG.KC.DecText CFSG.ComponentClassification.J2Cover.Models

theorem kFR : digitsOK FR.chars = true := by quickRfl

theorem fRows_eq : fRows = (natsK FR.chars).toArray := FR.eq.trans (natsOf_ofList kFR)

open Certificates in
open CFSG.ComponentClassification.J2Cover.Models in
theorem cert10026 :
    (bitAt fRows 2 16 && !bitAt fRows 16 2) = false ∧
      (!bitAt fRows 2 16 && bitAt fRows 16 2) = true := by
  rw [fRows_eq]
  decide +kernel

end CertificateChecks.KernelLC

end
