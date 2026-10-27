module

public import Certificates.Kernel.Om2K.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Holder1711.Om2Check
public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.SetOrb

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (wT)
open CertificateChecks.KernelLC.E8 (RT)

theorem kRT : allN 240 (fun r => canonK 240 8 (mask 8) (240 * 8) (RT r)) = true := by quickRfl

theorem kGY : allN 8 (fun i => Nat.beq (L.G i) (gYK i)) = true := by quickRfl

theorem kInv : allN 8 (fun i => Nat.beq (L.G (Nat.add i 8)) (pinv (L.G i))) = true := by quickRfl

theorem kOkL : allN 16 (fun l => okK (L.G l)) = true := by quickRfl

theorem kTG : allN 8 (fun k => Nat.beq (TG.G k)
    (wYK (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check.wT.getD k []))) = true := by
  quickRfl

theorem kWS : allN 12 (fun k => Nat.beq (WS.G k) (wYK (wSub.getD k []))) = true := by quickRfl

theorem kFU : allN 3 (fun k => Nat.beq (FU.G k) (wYK (wFuse0.getD k []))) = true := by quickRfl

theorem kOkTG : allN 8 (fun k => okK (TG.G k)) = true := by quickRfl

theorem kOkWS : allN 12 (fun k => okK (WS.G k)) = true := by quickRfl

theorem kOkFU : allN 3 (fun k => okK (FU.G k)) = true := by quickRfl

theorem kId : idK 480 9 (mask 9) = true := by quickRfl

theorem kPid : canonK 480 9 (mask 9) (480 * 9) pid = true := by quickRfl

theorem kId2 : idK 240 8 (mask 8) = true := by quickRfl

theorem kPid2 : canonK 240 8 (mask 8) (240 * 8) (pidn 240 8) = true := by quickRfl

end CertificateChecks.KernelOm2

end
