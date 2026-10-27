module

public import Certificates.Kernel.TwoHSLe4.S9Defs
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.S9

theorem sub0 : subChunk 0 = true := by quickRfl
theorem sub1 : subChunk 1 = true := by quickRfl
theorem sub2 : subChunk 2 = true := by quickRfl
theorem sub3 : subChunk 3 = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.S9

end
