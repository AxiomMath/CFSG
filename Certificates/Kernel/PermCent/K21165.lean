module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelInputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.K21165

open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] noncomputable def cnt21165 (X : CV 45) : Nat :=
  ((elemsC QP45).filter fun g => eq22C g X X g).length

theorem k21165 : Nat.beq (cnt21165 (cOf x45)) 576 = true := by decide +kernel

end CFSG.Certificates.Kernel.PkCV.K21165
