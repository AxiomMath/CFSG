module

public import Certificates.Data.Kernel.O8.T0
public import Certificates.Kernel.OmegaEight.S0Data
public import Certificates.Kernel.OmegaEight.OrthGens
public import Certificates.Kernel.OmegaEight.CorrGens
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KLie.CT

theorem kWords : wordsOK GPlus LPlus S0W = true := by quickRfl
theorem kUIdx : andB (Nat.beq (mat LPlus 4) (mat UPlus 3)) (andB (Nat.beq (mat LPlus 5) (mat UPlus 4))
    (Nat.beq (mat LPlus 6) (mat UPlus 5))) = true := by quickRfl
theorem kE0 : e0OK LPlus = true := by quickRfl
theorem kT0 : t0OK (ltK GPlus CPlus S0W) MTPlus YW = true := by quickRfl
theorem kComm : commOK (ltK GPlus CPlus S0W) MTPlus = true := by quickRfl

end CertificateChecks.KernelO8

end
