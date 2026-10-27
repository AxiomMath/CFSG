module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtSD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtND
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtNF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

local notation "pg11" => pg 11 (mask 11)

theorem kHd : btHdK SuzBtCL1.cnt = true := by quickRfl

theorem kCnt : SuzBtCL1.cnt = 3072 := by decide

theorem kSl0 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtCL1.cnt SuzBtCL1.B SuzBtCL1.G
    SuzBtCL1.K SuzBtCL1.R SuzBtCL1.POS 0 1024 = true := by quickRfl

theorem kSl1 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtCL1.cnt SuzBtCL1.B SuzBtCL1.G
    SuzBtCL1.K SuzBtCL1.R SuzBtCL1.POS 1024 1024 = true := by quickRfl

theorem kSl2 : btSlK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtCL1.cnt SuzBtCL1.B SuzBtCL1.G
    SuzBtCL1.K SuzBtCL1.R SuzBtCL1.POS 2048 1024 = true := by quickRfl

theorem kC : allN 4 (fun j => allN 4 (fun l => allN 3 (fun t =>
    Nat.beq (pg11 (SuzBtCL1.G j) (pg11 (SuzBtL1.G l) (pg11 SuzBtCL1.B t)))
      (pg11 (SuzBtL1.G l) (pg11 (SuzBtCL1.G j) (pg11 SuzBtCL1.B t)))))) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtNF

end
