module

public import Certificates.Data.Kernel.HeE8K
public import Certificates.Kernel.LocalComp.HeFix

public section

namespace CertificateChecks.KernelHeE8

open CFSG.KC.HeE8K CertificateChecks.KernelLC.HeFix

theorem k17486 : heE8OKF (evK (HG.F 0) (HG.F 1)) = true := by decide +kernel

end CertificateChecks.KernelHeE8
