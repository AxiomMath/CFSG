module

public import Certificates.Data.Kernel.HJ12KT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelHJ12

open Certificates.Kernel.HJ12K CFSG.KC.Mat12P CFSG.KC.Mat8P
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem ch17283_z : zQ = true := by quickRfl

theorem ch17283_tri : triQ = true := by quickRfl

theorem ch17283_a1 : fourQ (wordQ hj_b1Word) (wordQ hj_b2Word) (wordQ hj_g1Word) 81 = true := by
  quickRfl

theorem ch17283_a2 : fourQ (wordQ hj_c1Word) (wordQ hj_c2Word) (wordQ hj_h1Word) 136 = true := by
  quickRfl

end CertificateChecks.KernelHJ12
