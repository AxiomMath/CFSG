module

public import Certificates.Data.Kernel.HJ12K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelHJ12

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem ch17290_x7 : x7Q = true := by quickRfl

theorem ch17290_p3 : p3Q = true := by quickRfl

end CertificateChecks.KernelHJ12
