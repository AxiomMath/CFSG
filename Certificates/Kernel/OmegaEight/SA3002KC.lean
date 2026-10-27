module

public import Certificates.Kernel.OmegaEight.SA3002K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEightMinus

theorem kClosedM0 : allBlk 0 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM1 : allBlk 1024 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM2 : allBlk 2048 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM3 : allBlk 3072 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM4 : allBlk 4096 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM5 : allBlk 5120 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM6 : allBlk 6144 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl
theorem kClosedM7 : allBlk 7168 (saClosedAtG 6 saCodes saMulT saGenT) 1024 = true := by quickRfl

end CertificateChecks.KernelO8

end
