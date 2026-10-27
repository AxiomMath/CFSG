module

public import Certificates.Kernel.OmegaEight.E4O8MembersK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight

theorem kE4Twins : bAnd(e4EdgeAt (wO (e4WW 3)), e4DiffAt (wO (e4WW 1)) (wO (e4WW 3))) = true := by
  quickRfl

end CertificateChecks.KernelO8

end
