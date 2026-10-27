module

public import Certificates.Data.Kernel.J4Loc.Stab
public import Certificates.Kernel.J4Loc.StabData
public import CFSG.Sporadic.J4.QTData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Loc CFSG.KD.J4Loc

theorem ch4178_ok : stabOK CFSG.Sporadic.J4.QT.letterRows ST4178 = true := by
  quickRfl

theorem ch4178_cov : stabCov [0, 422, 553, 911, 1131, 1485, 1602, 2020] ST4178 = true := by
  quickRfl

end CertificateChecks.KernelJ4Loc

end
