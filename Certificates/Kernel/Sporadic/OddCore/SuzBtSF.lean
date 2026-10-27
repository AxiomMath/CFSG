module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtSD
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtSF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kHd : btHdK SuzBtS1.cnt = true := by quickRfl

theorem kCnt : SuzBtS1.cnt = 8192 := by decide

theorem kSl0 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 0 1024 = true := by quickRfl

theorem kSl1 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 1024 1024 = true := by quickRfl

theorem kSl2 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 2048 1024 = true := by quickRfl

theorem kSl3 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 3072 1024 = true := by quickRfl

theorem kSl4 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 4096 1024 = true := by quickRfl

theorem kSl5 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 5120 1024 = true := by quickRfl

theorem kSl6 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 6144 1024 = true := by quickRfl

theorem kSl7 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B SuzBtS1.G
    SuzBtS1.K SuzBtS1.R SuzBtS1.POS 7168 1024 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtSF

end
