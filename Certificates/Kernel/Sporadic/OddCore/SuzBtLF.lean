module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtLD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtOD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Data.Kernel.Spor.BTupS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtLF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kSg : allN 2 (fun j => btSgK 11 (mask 11) 3 33 (mask 33) SuzBtL1.cnt 4 (mask 4) SuzBtL1.G
    SuzBtL1.K SuzBtL1.R SuzBtM1O.PRE (SuzBtLS.G j) (SuzBtM1O.C j) j) = true := by quickRfl

theorem kSB : allN 4 (fun i => strictB (pg 4 (mask 4) SuzBtLS.B i) (fun u =>
    bAnd(Nat.blt u SuzBtL1.cnt, btMov 11 (mask 11) 3 (SuzBtL1.G i) SuzBtL1.B
      (btKey 33 (mask 33) SuzBtL1.K u)))) = true := by quickRfl

theorem kLCnt : SuzBtLS.cnt = 24 := rfl

theorem kLSl : btSlK 16 4 (mask 4) 4 16 (mask 16) 2 SuzBtLS.cnt SuzBtLS.B SuzBtLS.G SuzBtLS.K
    SuzBtLS.R SuzBtLS.POS 0 24 = true := by quickRfl

theorem kInc : btIncK 45 SuzBtLC.SV = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtLF

end
