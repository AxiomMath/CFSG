module

public import Certificates.Data.Kernel.U43Swap.Defs
public import Certificates.Kernel.U43Swap.Data
public import Certificates.Kernel.U43Mod.Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Swap

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Swap CFSG.KS CertificateChecks.KernelU43Mod

theorem kP : allN 4 (fun e => bAnd(permOK 820 10 (mask 10) (820 * 10) (PT e) (PT (Nat.add e 4)),
    bAnd(inPU (PT e), baseEq bs (pg 10 (mask 10) (PT e)) (GM e)))) = true := by
  quickRfl

theorem kU : eqB (fun q => lp PT 2 (lp PT 2 q)) (fun q => q) = true := by quickRfl

theorem kOKey : allN 81 (oKey PT OD) = true := by quickRfl

theorem kOCl : allN 81 (oCl PT OD) = true := by quickRfl

theorem kOYm : allN 81 (oYm PT OD YR) = true := by quickRfl

theorem kOT2 : allN 81 (oT2 PT OD YR) = true := by quickRfl

theorem kZ : zOK PT OD ZI = true := by quickRfl

theorem kY : allN 8 (yRec PT OD YR) = true := by quickRfl

theorem kQ : allN 64 (qRec PT QR) = true := by quickRfl

theorem kT : allN 8 (tRec PT YR TW) = true := by quickRfl

theorem kN : allN 64 (nRec PT OD NW) = true := by quickRfl

theorem kK : allN 128 (kRec PT KC) = true := by quickRfl

end CertificateChecks.KernelU43Swap

end
