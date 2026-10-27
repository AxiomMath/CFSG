module

public import Certificates.Kernel.J4Q.MaskData
public import CFSG.Sporadic.J4.QTRankNative
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4Loc

open CFSG.Sporadic.J4.QT CFSG.KD.J4Q

theorem ch4174_kinv :
    ((List.range 4).all fun i => compT (mkKIT.getD i []) (mkKT.getD i []) == idT) = true := by
  quickRfl

theorem neg4174_kinv : (!(compT (mkKIT.getD 0 []) (mkKT.getD 1 []) == idT)) = true := by
  quickRfl

end CertificateChecks.KernelJ4Loc

end
