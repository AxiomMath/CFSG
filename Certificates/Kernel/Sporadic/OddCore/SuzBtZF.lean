module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtZF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

local notation "pg11" => pg 11 (mask 11)

theorem kL1Hd : btHdK SuzBtL1.cnt = true := by quickRfl

theorem kL1Cnt : SuzBtL1.cnt = 16 := by decide

theorem kL1Sl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtL1.cnt SuzBtL1.B SuzBtL1.G
    SuzBtL1.K SuzBtL1.R SuzBtL1.POS 0 16 = true := by quickRfl

theorem kL1C : allN 4 (fun j => allN 4 (fun l => allN 3 (fun t =>
    Nat.beq (pg11 (SuzBtL1.G j) (pg11 (SuzBtL1.G l) (pg11 SuzBtL1.B t)))
      (pg11 (SuzBtL1.G l) (pg11 (SuzBtL1.G j) (pg11 SuzBtL1.B t)))))) = true := by quickRfl

theorem kL1I : allN 4 (fun j => allN 3 (fun t =>
    Nat.beq (pg11 (SuzBtL1.G j) (pg11 (SuzBtL1.G j) (pg11 SuzBtL1.B t))) (pg11 SuzBtL1.B t))) =
    true := by quickRfl

theorem kT : allN 4 (fun j => bAnd(Nat.blt (SuzBtM1Z.T j) SuzBtM1.cnt,
    btMov 11 (mask 11) 3 (SuzBtL1.G j) SuzBtM1.B (btKey 33 (mask 33) SuzBtM1.K (SuzBtM1Z.T j)))) =
    true := by quickRfl

theorem kC : allN 4 (fun j => allN 8 (fun l => allN 3 (fun t =>
    Nat.beq (pg11 (SuzBtL1.G j) (pg11 (SuzBtM1.G l) (pg11 SuzBtM1.B t)))
      (pg11 (SuzBtM1.G l) (pg11 (SuzBtL1.G j) (pg11 SuzBtM1.B t)))))) = true := by quickRfl

theorem kS : allN 8 (fun j => btMov 11 (mask 11) 3 (SuzBtM1.G j) SuzBtM1.B
    (btKey 33 (mask 33) SuzBtM1.K (SuzBtM1Z.S j))) = true := by quickRfl

theorem kRt : btRtSlK 8 8 SuzBtM1.cnt SuzBtM1Z.S SuzBtM1.R SuzBtM1.POS SuzBtM1Z.RT 0 1024 =
    true := by quickRfl

theorem kCz : btCzSlK 11 (mask 11) 3 33 (mask 33) 8 SuzBtM1.cnt SuzBtL1.cnt SuzBtM1.G SuzBtM1.K
    SuzBtM1Z.RT SuzBtL1.K SuzBtM1Z.IX 0 1024 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtZF

end
