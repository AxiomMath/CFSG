module

public import Certificates.Kernel.L34W.Outer
public import Certificates.Data.Kernel.L34W.HjFix

public section

namespace CertificateChecks.KernelL34W

open CFSG.KC.Enum CFSG.KS CFSG.KC.L34W

theorem hj_k : hjK T1X.F AlX.F YT = true := by decide +kernel

end CertificateChecks.KernelL34W

end
