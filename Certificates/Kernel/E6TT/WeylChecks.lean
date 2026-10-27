module

public import Certificates.Data.Kernel.E6TT.Weyl
public import Certificates.Kernel.E6TT.WeylData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT Certificates.Data.E6TableT

theorem weylA2 : wOKK (classes (reps.getD 0 [])) W.H0 W.O0 = true := by quickRfl

theorem weylA4A1 : wOKK (classes (reps.getD 1 [])) W.H1 W.O1 = true := by quickRfl

theorem weylD4 : wOKK (classes (reps.getD 2 [])) W.H2 W.O2 = true := by quickRfl

theorem weylA5 : wOKK (classes (reps.getD 3 [])) W.H3 W.O3 = true := by quickRfl

theorem weylD5 : wOKK (classes (reps.getD 4 [])) W.H4 W.O4 = true := by quickRfl

end CertificateChecks.KernelE6TT

end
