module

public import Certificates.Data.Kernel.L34M64.Twin
public import Certificates.Kernel.L34M64.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelL34M64

open CFSG.KC.L34M64 CFSG.KD.L34M64 CFSG.Quasithin.H13.Ch9.L34M

theorem ch7258four :
    (DAT.all fun d => AllLt 64 d.1 && rankOKK 4 64 d.1 (pickWitK 64 4 d.1)) = true := by
  quickRfl

end CertificateChecks.KernelL34M64
