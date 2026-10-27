module

public import Certificates.Kernel.TwoHSLe4.S9Defs
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.S9

theorem sub8 : subChunk 8 = true := by quickRfl
theorem sub9 : subChunk 9 = true := by quickRfl
theorem sub10 : subChunk 10 = true := by quickRfl
theorem sub11 : subChunk 11 = true := by quickRfl

end CertificateChecks.KernelTwoHSLe4.S9

end
