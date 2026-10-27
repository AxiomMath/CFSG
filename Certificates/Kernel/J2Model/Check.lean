module

public import Certificates.Data.Kernel.J2ModelK
public import Certificates.Kernel.J2Cover.OrbData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelJ2Model

open CFSG.KC.J2ModelK CertificateChecks.KernelJ2Cover

theorem chk : modelK 315 9 ALP BEP = true := by quickRfl

theorem permA : CFSG.KC.Misc.ArrEnum.permB 315 9 ALP = true := by quickRfl

theorem permB' : CFSG.KC.Misc.ArrEnum.permB 315 9 BEP = true := by quickRfl

end CertificateChecks.KernelJ2Model
