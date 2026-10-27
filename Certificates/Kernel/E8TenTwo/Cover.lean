module

public import Certificates.Data.Kernel.E8TenTwoBits
public import Certificates.Kernel.E8TenTwo.Data

public section

namespace CertificateChecks.KernelE8TenTwo

open CFSG.KC.E8TenTwoBits

theorem coverOK_bits : coverOK 20 bitsData = true := by decide +kernel

end CertificateChecks.KernelE8TenTwo

end
