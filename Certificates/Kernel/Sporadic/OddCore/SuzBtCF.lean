module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtSD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtSZD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtCD
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtCF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

local notation "cls" => btClsSlK 4 SuzBtS1.cnt SuzBtS1C.r0 33 (mask 33) SuzBtL1.cnt SuzBtS1.K
  SuzBtS1.R SuzBtS1Z.RT SuzBtL1.K SuzBtS1C.TG SuzBtS1C.E

theorem kHd : btClsHdK SuzBtS1.cnt SuzBtS1C.r0 SuzBtS1.R = true := by quickRfl

theorem kCl0 : cls 0 1024 = true := by quickRfl

theorem kCl1 : cls 1024 1024 = true := by quickRfl

theorem kCl2 : cls 2048 1024 = true := by quickRfl

theorem kCl3 : cls 3072 1024 = true := by quickRfl

theorem kCl4 : cls 4096 1024 = true := by quickRfl

theorem kCl5 : cls 5120 1024 = true := by quickRfl

theorem kCl6 : cls 6144 1024 = true := by quickRfl

theorem kCl7 : cls 7168 1024 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtCF

end
