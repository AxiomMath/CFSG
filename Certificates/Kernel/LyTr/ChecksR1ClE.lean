module

public import Certificates.Kernel.LyTr.Defs1080
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.LyTr.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyTr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH

theorem k_r1cl16 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 31104 1944 =
    true := by quickRfl

theorem k_r1cl17 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 33048 1944 =
    true := by quickRfl

theorem k_r1cl18 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 34992 1944 =
    true := by quickRfl

theorem k_r1cl19 : slK (Nat.mul R1.cnt 10)
    (findPtK R1.cnt R1.T (prodQK 1080 11 (mask 11) 10 R1.T (bothK 5 R1.GI R1I)) R1Cl) 36936 1944 =
    true := by quickRfl

end CertificateChecks.KernelLyTr

end
