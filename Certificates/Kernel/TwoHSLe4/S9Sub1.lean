module

public import Certificates.Kernel.TwoHSLe4.S9Defs
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.S9

theorem sub4 : subChunk 4 = true := by quickRfl
theorem sub5 : subChunk 5 = true := by quickRfl
theorem sub6 : subChunk 6 = true := by quickRfl
theorem sub7 : subChunk 7 = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.S9

end
