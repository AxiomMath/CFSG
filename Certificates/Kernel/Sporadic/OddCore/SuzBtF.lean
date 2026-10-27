module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kHd : btHdK SuzBtM1.cnt = true := by quickRfl

theorem kCnt : SuzBtM1.cnt = 1024 := by decide

theorem kSl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 8 SuzBtM1.cnt SuzBtM1.B SuzBtM1.G
    SuzBtM1.K SuzBtM1.R SuzBtM1.POS 0 1024 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtF

end
