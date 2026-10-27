module

public import Certificates.Kernel.SporSch.Co2S.ItChain
public import Certificates.Data.Kernel.SporSch.BaseBound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2It

open CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix CertificateChecks.KernelSporSch

theorem pnb : Co2ItC.pnb = 9 := rfl

theorem bb : Nat.beq (bbProd 12 (bbMask co2ItNat) Co2ItC.LR Co2ItC.BP 9) 41287680 = true := by
  quickRfl

theorem mk : maskOK 2300 (bbMask co2ItNat) co2ItNat = true := by quickRfl

end CertificateChecks.KernelSporSch.Co2It

end
