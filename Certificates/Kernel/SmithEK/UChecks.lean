module

public import Certificates.Data.Kernel.SmithEKU
public import Certificates.Kernel.SmithEK.UData
public import Certificates.Kernel.SmithEK.WData

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem c21263dual : dualK wData.toList ua.Y = true := by
  decide +kernel

theorem c21263key : keyK wd.M ua.R = true := by
  decide +kernel

end CertificateChecks.KernelSmithEK
