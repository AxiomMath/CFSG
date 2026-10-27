module

public import Certificates.Kernel.HS799102.ClassData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Misc.ArrEnum

theorem ch799102_bind : pGBind = true := by quickRfl

theorem ch799102_perm : CFSG.KC.Enum.allN 4 (fun k => permB 100 7 (pG k)) &&
    CFSG.KC.Enum.allN 9 (fun k => permB 100 7 (TH.F k)) = true := by quickRfl

theorem ch799102_c1 : classK 100 7 pG pGI 4 (TH.F 2) R1 = true := by quickRfl

theorem ch799102_c2 : classK 100 7 pG pGI 4 (TH.F 3) R2 = true := by quickRfl

theorem ch799102_len : Nat.beq R1.length 1100 && Nat.beq R2.length 1100 &&
    Nat.beq R3.length 15400 = true := by quickRfl

end CertificateChecks.KernelHS799102

end
