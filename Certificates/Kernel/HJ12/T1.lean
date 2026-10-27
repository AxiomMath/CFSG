module

public import Certificates.Data.Kernel.HJ12KT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelHJ12

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem ch17292_tau : tauQCheck = true := by quickRfl

theorem ch17292_t1 : t1Q = true := by quickRfl

end CertificateChecks.KernelHJ12
