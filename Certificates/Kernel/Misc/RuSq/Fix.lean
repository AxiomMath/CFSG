module

public import Certificates.Kernel.Misc.RuSq.Chain
public import Certificates.Kernel.Misc.RuSq.Hints
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.RuSq

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuSq

theorem fixOK : fix2K 4060 12 (mask 12) (4060 * 12) RuSqS.LR RuSqS.TR hintsK = true := by
  quickRfl

end CertificateChecks.KernelMisc.RuSq

end
