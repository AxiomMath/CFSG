module

public import Certificates.Kernel.KGC31M24.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3
open CFSG.Quasithin.KGC31.M24 CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M24OC

theorem kOrd5 : pord 24 5 5 X5 = true := by quickRfl
theorem kOrd7 : pord 24 5 7 X7 = true := by quickRfl
theorem kOrd11 : pord 24 5 11 X11 = true := by quickRfl
theorem kOrd23 : pord 24 5 23 X23 = true := by quickRfl

theorem kN : Nat.beq RI.N 43263 = true := by quickRfl

theorem kCS : RI.CS = [31878, 11385] := by decide +kernel

theorem kOff : offOK RI.CS RI.OFF RI.N = true := by quickRfl

theorem kGP : (Nat.beq (RI.GP 0) (M24Q.S 0) && Nat.beq (RI.GP 1) (M24Q.S 1)) = true := by quickRfl

theorem kGIP : (permOK 24 5 (mask 5) (24 * 5) (M24Q.S 0) (RI.GIP 0) &&
    permOK 24 5 (mask 5) (24 * 5) (M24Q.S 1) (RI.GIP 1)) = true := by quickRfl

theorem kGc : (canonK 24 5 (mask 5) (24 * 5) (RI.GP 0) && canonK 24 5 (mask 5) (24 * 5) (RI.GIP 0) &&
    canonK 24 5 (mask 5) (24 * 5) (RI.GP 1) && canonK 24 5 (mask 5) (24 * 5) (RI.GIP 1)) =
    true := by quickRfl

theorem kQS : (Nat.beq (QQ.S 0) (pw (qGenW.getD 0 [])) && Nat.beq (QQ.S 1) (pw (qGenW.getD 1 [])) &&
    Nat.beq (QQ.S 2) (pw (qGenW.getD 2 [])) && Nat.beq (QQ.S 3) (pw (qGenW.getD 3 []))) = true := by
  quickRfl

theorem kQN : Nat.beq (CFSG.KS.SporSch.MOC.ordK QQ.LR 2) 128 = true := by quickRfl

end CertificateChecks.KernelKGC31M24

end
