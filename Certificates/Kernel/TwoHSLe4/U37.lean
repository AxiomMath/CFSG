module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUU37
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTwoHSLe4

open CFSG.EvenSporadicStandard.TwoHS

set_option maxHeartbeats 0 in
theorem u3Check_true : u3Check = true := by quickRfl

set_option maxHeartbeats 0 in
theorem u7Check_true : u7Check = true := by quickRfl

set_option maxHeartbeats 0 in
theorem u7ex_true : u7ex = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4
