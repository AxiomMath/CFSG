module

public import Certificates.Kernel.LyTr.Defs1080
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LyTr.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH

theorem k_r1cl4 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 7776 1944 =
    true := by quickRfl

theorem k_r1cl5 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 9720 1944 =
    true := by quickRfl

theorem k_r1cl6 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 11664 1944 =
    true := by quickRfl

theorem k_r1cl7 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 13608 1944 =
    true := by quickRfl

end CertificateChecks.KernelLyTr

end
