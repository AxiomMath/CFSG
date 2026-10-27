module

public import Certificates.Kernel.FiveStd.Diag
public import Certificates.Data.Kernel.FiveStdKDiag2
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

theorem diag0v : dvOK A0 25 (CB.getD 0 0) 100 = true := by quickRfl

theorem diag1v : dvOK A1 25 (CB.getD 1 0) 100 = true := by quickRfl

end CertificateChecks.FiveStd

end
