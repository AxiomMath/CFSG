module

public import Certificates.Kernel.TwoHSLe4.S9Defs
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.S9

theorem sub12 : subChunk 12 = true := by quickRfl
theorem sub13 : subChunk 13 = true := by quickRfl
theorem sub14 : subChunk 14 = true := by quickRfl
theorem sub15 : subChunk 15 = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.S9

end
