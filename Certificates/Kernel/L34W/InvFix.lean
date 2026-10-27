module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Data.Kernel.L34W.InvFix

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W

theorem cf22_k : cf22K T1X.F AlX.F YT = true := by decide +kernel

end CertificateChecks.KernelL34W

end
