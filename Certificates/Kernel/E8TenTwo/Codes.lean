module

public import Certificates.Data.Kernel.E8TenTwoBits
public import Certificates.Kernel.E8TenTwo.Data

public section

namespace CertificateChecks.KernelE8TenTwo

open CFSG.KC.E8TenTwoBits

theorem codesOK_bits : codesOK bitsData = true := by decide +kernel

end CertificateChecks.KernelE8TenTwo

end
