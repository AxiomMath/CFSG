module

public import Certificates.Data.PSp43Sylow
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import Certificates.Data.Kernel.PermCent.SealPSp43

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelSchreierFam

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkEnum.Seal

theorem qt0_23100K : schP QT0 = true ∧ orderV QT0 = 64 := by
  simp only [schP, orderV, qT0_strong]
  constructor <;> decide +kernel

theorem cent_23100K :
    (((elemsV QT0).filter fun g => decide (g * g = 1) && decide (g ≠ 1)).filter fun g =>
      ((elemsV QT0).filter fun g => decide (g * g = 1) && decide (g ≠ 1)).all fun t =>
        decide (g * t = t * g)).length = 1 := by
  decide +kernel

end CertificateChecks.KernelSchreierFam
