module

public import Certificates.Data.Kernel.J4Loc.C15
public import Certificates.Kernel.J4Loc.TrioData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Loc CFSG.KD.J4Loc

theorem ch4179 : c15K TRK TRR 3795 [0, 1, 5, 3, 2, 2, 4] [4, 0, 4, 3, 1, 0, 1, 5] = true := by
  quickRfl

end CertificateChecks.KernelJ4Loc

end
