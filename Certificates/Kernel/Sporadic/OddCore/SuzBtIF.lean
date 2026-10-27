module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Data.Kernel.Spor.BTupI
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtIF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kI : Nat.beq (btCntN SuzBtM1.cnt (btInvP 8 33 (mask 33) SuzBtL1.cnt SuzBtM1.K SuzBtM1.R
    SuzBtM1Z.RT SuzBtL1.K)) 288 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtIF

end
