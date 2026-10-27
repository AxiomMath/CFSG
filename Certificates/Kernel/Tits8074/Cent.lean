module

public import Certificates.Kernel.Tits8074.Data
public import Certificates.Data.Kernel.Tits8074
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074

theorem cen : cenZ L zc = true := by quickRfl

theorem conj : conjB L 0 aw zc = true := by quickRfl

theorem pair : pairK L sc = true := by quickRfl

theorem orb2 : orbK L r2 [0, 3] 1 = true := by quickRfl
theorem orb3 : orbK L r3 [0, 3, 1] 5 = true := by quickRfl
theorem orb4 : orbK L r4 [0, 3, 1, 5] 6 = true := by quickRfl
theorem orb5 : orbK L r5 [0, 3, 1, 5, 6] 12 = true := by quickRfl
theorem orb6 : orbK L r6 [0, 3, 1, 5, 6, 12] 24 = true := by quickRfl

theorem zs0 : zsK L zc sc false r2 r3 r4 r5 r6 = true := by quickRfl
theorem zs1 : zsK L zc sc true r2 r3 r4 r5 r6 = true := by quickRfl

end CertificateChecks.KernelT8074

end
