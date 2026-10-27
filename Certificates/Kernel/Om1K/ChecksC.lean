module

public import Certificates.Kernel.Om1K.OrbDefs
public meta import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum CFSG.KC.SetOrb CFSG.KC.BfsPin CFSG.KS
open CertificateChecks.KernelLC.E8 (FT NEG)

theorem kNA : OA.N = 3780 := rfl

theorem kDistA : distinctK 3780 (fun i => keyK 240 8 4 (OA.C i)) OA.S = true := by quickRfl

theorem kFa : Nat.beq (eqMaskK 240 8 (FT 3) NEG) (OA.M 0) = true := by quickRfl

theorem kNR : RO.N = 240 := rfl

theorem kRO : allN 240 roOK = true := by quickRfl

theorem kDistR : distinctK 240 (fun i => keyK 240 8 1 (RO.C i)) RO.S = true := by quickRfl

theorem kRoot : Nat.beq rootK (pg 8 (mask 8) (OC.C 0) 0) = true := by quickRfl

theorem kTT : allN 240 ttOK = true := by quickRfl

theorem kNG : SG.ng = 10 := rfl

theorem kSG : allN 10 sgOK = true := by quickRfl

theorem kNC : OC.N = 3780 := rfl

theorem kDistC : distinctK 3780 (fun i => keyK 240 8 8 (OC.C i)) OC.S = true := by quickRfl

theorem kFc : Nat.beq (eqMaskK 240 8 (FT 23) NEG) (OC.M 0) = true := by quickRfl

end CertificateChecks.KernelOm1.A

#kc_each CertificateChecks.KernelOm1.A.oaOKc 0 63
#kc_each CertificateChecks.KernelOm1.A.ocOKc 0 63

end
