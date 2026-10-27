module

public import Certificates.Kernel.Tits8074.Grp
public import Certificates.Kernel.Tits8074.Data
public import Certificates.Data.Kernel.Tits8074Grp
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelT8074

open CFSG.KC.Tits8074

theorem hEq : genEq L HG.G hw 0 = true := by quickRfl

theorem tEq : genEq L TG.G tg 0 = true := by quickRfl

theorem hComm : commG L HG.G 2 2 = true := by quickRfl

theorem tConj : conjK L TG.T cw 0 = true := by quickRfl

end CertificateChecks.KernelT8074

end
