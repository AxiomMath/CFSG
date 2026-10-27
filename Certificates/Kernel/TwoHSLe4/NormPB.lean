module

public import Certificates.Kernel.TwoHSLe4.NormP
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.NormP

open CFSG.EvenSporadicStandard.TwoHS CertificateChecks.KernelTwoHSLe4.Norm

theorem candK_ok : (candK == candData.map S9.rl) = true := by quickRfl

theorem nb0 : chkN (svR 0) = true := by quickRfl
theorem nb1 : chkN (svR 1) = true := by quickRfl
theorem nb2 : chkN (svR 2) = true := by quickRfl
theorem nb3 : chkN (svR 3) = true := by quickRfl
theorem nb4 : chkN (svR 4) = true := by quickRfl
theorem nb5 : chkN (svR 5) = true := by quickRfl
theorem nb6 : chkN (svR 6) = true := by quickRfl
theorem nb7 : chkN (svR 7) = true := by quickRfl
theorem nb8 : chkN (svR 8) = true := by quickRfl
theorem nb9 : chkN (svR 9) = true := by quickRfl
theorem nb10 : chkN (svR 10) = true := by quickRfl
theorem nb11 : chkN (svR 11) = true := by quickRfl
theorem nb12 : chkN (svR 12) = true := by quickRfl
theorem nb13 : chkN (svR 13) = true := by quickRfl
theorem nb14 : chkN (svR 14) = true := by quickRfl
theorem nb15 : chkN (svR 15) = true := by quickRfl
theorem nb16 : chkN (svR 16) = true := by quickRfl
theorem nb17 : chkN (svR 17) = true := by quickRfl
theorem nb18 : chkN (svR 18) = true := by quickRfl
theorem nb19 : chkN (svR 19) = true := by quickRfl
theorem nb20 : chkN (svR 20) = true := by quickRfl
theorem nb21 : chkN (svR 21) = true := by quickRfl
theorem nb22 : chkN (svR 22) = true := by quickRfl
theorem nb23 : chkN (svR 23) = true := by quickRfl
theorem nb24 : chkN (svR 24) = true := by quickRfl
theorem nb25 : chkN (svR 25) = true := by quickRfl
theorem nb26 : chkN (svR 26) = true := by quickRfl
theorem nb27 : chkN (svR 27) = true := by quickRfl
theorem nb28 : chkN (svR 28) = true := by quickRfl
theorem nb29 : chkN (svR 29) = true := by quickRfl
theorem nb30 : chkN (svR 30) = true := by quickRfl
theorem nb31 : chkN (svR 31) = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.NormP

end
