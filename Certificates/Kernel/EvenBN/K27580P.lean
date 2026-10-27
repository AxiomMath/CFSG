module

public import Certificates.Kernel.EvenBN.K27580D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN.E32

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor

theorem lK : SI.L.all (fun A => canonK 1755 11 (mask 11) (1755 * 11) A && sS A) = true := by
  quickRfl

theorem p0 : (SI.L.take 36).all pivK = true := by quickRfl
theorem p1 : ((SI.L.drop 36).take 36).all pivK = true := by quickRfl
theorem p2 : ((SI.L.drop 72).take 36).all pivK = true := by quickRfl
theorem p3 : (SI.L.drop 108).all pivK = true := by quickRfl

end CertificateChecks.KernelEvenBN.E32

end
