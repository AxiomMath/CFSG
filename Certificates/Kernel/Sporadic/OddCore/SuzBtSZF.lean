module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtSD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtSZD
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtSZF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

theorem kT1Cnt : SuzBtT1.cnt = 2 := by decide

theorem kT1Sl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 1 SuzBtT1.cnt SuzBtT1.B SuzBtT1.G
    SuzBtT1.K SuzBtT1.R SuzBtT1.POS 0 2 = true := by quickRfl

theorem kZS : allN 4 (fun j => btMov 11 (mask 11) 3 (SuzBtS1.G j) SuzBtS1.B
    (btKey 33 (mask 33) SuzBtS1.K (SuzBtS1Z.S j))) = true := by quickRfl

theorem kZRt0 : btRtSlK 4 4 SuzBtS1.cnt SuzBtS1Z.S SuzBtS1.R SuzBtS1.POS SuzBtS1Z.RT 0 4096 =
    true := by quickRfl

theorem kZRt1 : btRtSlK 4 4 SuzBtS1.cnt SuzBtS1Z.S SuzBtS1.R SuzBtS1.POS SuzBtS1Z.RT 4096 4096 =
    true := by quickRfl

theorem kZCz0 : btCzSlK 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtT1.cnt SuzBtS1.G
    SuzBtS1.K SuzBtS1Z.RT SuzBtT1.K SuzBtS1Z.IX 0 4096 = true := by quickRfl

theorem kZCz1 : btCzSlK 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtT1.cnt SuzBtS1.G
    SuzBtS1.K SuzBtS1Z.RT SuzBtT1.K SuzBtS1Z.IX 4096 4096 = true := by quickRfl

theorem kZT : bAnd(Nat.blt (SuzBtS1Z.T 0) SuzBtS1.cnt, btMov 11 (mask 11) 3 (SuzBtT1.G 0)
    SuzBtS1.B (btKey 33 (mask 33) SuzBtS1.K (SuzBtS1Z.T 0))) = true := by quickRfl

theorem kLS : allN 4 (fun j => btMov 11 (mask 11) 3 (SuzBtL1.G j) SuzBtS1.B
    (btKey 33 (mask 33) SuzBtS1.K (SuzBtS1L.S j))) = true := by quickRfl

theorem kLRt0 : btRtSlK 4 4 SuzBtS1.cnt SuzBtS1L.S SuzBtS1.R SuzBtS1.POS SuzBtS1L.RT 0 4096 =
    true := by quickRfl

theorem kLRt1 : btRtSlK 4 4 SuzBtS1.cnt SuzBtS1L.S SuzBtS1.R SuzBtS1.POS SuzBtS1L.RT 4096 4096 =
    true := by quickRfl

theorem kLCz0 : btCzSlK 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtM1.cnt SuzBtL1.G
    SuzBtS1.K SuzBtS1L.RT SuzBtM1.K SuzBtS1L.IX 0 4096 = true := by quickRfl

theorem kLCz1 : btCzSlK 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtM1.cnt SuzBtL1.G
    SuzBtS1.K SuzBtS1L.RT SuzBtM1.K SuzBtS1L.IX 4096 4096 = true := by quickRfl

theorem kLT : allN 8 (fun j => bAnd(Nat.blt (SuzBtS1L.T j) SuzBtS1.cnt,
    btMov 11 (mask 11) 3 (SuzBtM1.G j) SuzBtS1.B (btKey 33 (mask 33) SuzBtS1.K (SuzBtS1L.T j)))) =
    true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtSZF

end
