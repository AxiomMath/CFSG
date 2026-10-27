module

public import Certificates.Kernel.SporSch.HeT.Q2117K
public meta import Certificates.Kernel.SporSch.HeT.Q2117K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeQ17

meta def QCCsrc : Array Nat := CFSG.KS.SporSch.ChainClsG.commCounts 98 SQC baseQC tauM 2048

end CertificateChecks.KernelSporSch.HeQ17

#kss_list CertificateChecks.KernelSporSch.HeQ17.QCC.CS CertificateChecks.KernelSporSch.HeQ17.QCCsrc

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.ChainCls

@[expose] noncomputable def QCC.cntB (s : Nat) : Bool :=
  Nat.beq (commCntK 98 7 (mask 7) (98 * 7) (pidn 98 7) QC.LR QC.TR 4 QD.S 3 (ordK QC.LR 4)
    (s * 2048) 2048) (QCC.CS.getD s 0)

end CertificateChecks.KernelSporSch.HeQ17

#kss_each CertificateChecks.KernelSporSch.HeQ17.QCC.E CertificateChecks.KernelSporSch.HeQ17.QCC.cntB 8

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.ChainCls

theorem kCC : bAnd(Nat.ble (ordK QC.LR 4) (Nat.mul QCC.CS.length 2048), Nat.beq QCC.CS.sum 3) =
    true := by quickRfl

theorem negCC : (Nat.beq (commCntK 98 7 (mask 7) (98 * 7) (pidn 98 7) QC.LR QC.TR 4 QD.S 3
    (ordK QC.LR 4) 0 2048) (QCC.CS.getD 0 0 + 1)).not = true := by quickRfl

end CertificateChecks.KernelSporSch.HeQ17

end
