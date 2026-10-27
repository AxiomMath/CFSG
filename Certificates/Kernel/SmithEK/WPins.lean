module

public import Certificates.Data.Kernel.SmithEKW
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue

#kc_each CertificateChecks.KernelSmithEK c21104pin_
  (fun c => CFSG.SmithE.K.pinChunkK CFSG.SmithE.wData.toList CertificateChecks.KernelSmithEK.wd.W
    CertificateChecks.KernelSmithEK.wd.M (64 * c) 64) 0 14

public section

namespace CertificateChecks.KernelSmithEK

theorem wd_ok : CFSG.SmithE.K.wListOK wd.W = true := by
  decide +kernel

theorem wd_len : wd.W.length = 891 := by
  decide +kernel

theorem wData_len : CFSG.SmithE.wData.toList.length = 891 := by
  decide +kernel

end CertificateChecks.KernelSmithEK
