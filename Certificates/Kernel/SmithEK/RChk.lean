module

public import Certificates.Data.Kernel.SmithEKR
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.WData

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21261rank : chkRankK pb.P = true := by
  decide +kernel

theorem c21261span : chkSpanWK wd.W = true := by
  decide +kernel

end CertificateChecks.KernelSmithEK
