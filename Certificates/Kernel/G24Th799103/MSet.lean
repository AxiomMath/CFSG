module

public import Certificates.Kernel.G24Th799103.MData
public import Certificates.Data.Kernel.PCentSetF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24Th

open CFSG.KC.PCent

theorem ch799103_mst : setOrbK 1365 11 aG 3 TM ST = true := by
  rw [setOrbK_eq_F]
  quickRfl

end CertificateChecks.KernelG24Th

end
