module

public import Certificates.Kernel.HS799102.ChainData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Misc.ArrEnum

theorem ch799102_tperm : CFSG.KC.Enum.allN 21 (fun k => permB 100 7 (TV1.F k)) &&
    CFSG.KC.Enum.allN 23 (fun k => permB 100 7 (TV2.F k)) &&
    CFSG.KC.Enum.allN 21 (fun k => permB 100 7 (TV3.F k)) = true := by quickRfl

theorem ch799102_o1 : oddOrbK 100 7 dG1 2 X1 (maskK O1) O1 = true := by quickRfl

theorem ch799102_o2 : oddOrbK 100 7 dG2 2 X2 (maskK O2) O2 = true := by quickRfl

theorem ch799102_o3 : oddOrbK 100 7 dG3 2 X3 (maskK O3) O3 = true := by quickRfl

end CertificateChecks.KernelHS799102

end
