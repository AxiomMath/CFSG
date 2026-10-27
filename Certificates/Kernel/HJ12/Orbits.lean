module

public import Certificates.Data.Kernel.HJ12Orb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelHJ12

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem ch17291_orb : orbQ = true := by quickRfl

theorem ch17291_s1 : s1Q = true := by quickRfl

theorem ch17291_s2 : s2Q = true := by quickRfl

theorem ch17291_gam : gamQ = true := by quickRfl

end CertificateChecks.KernelHJ12
