module

public import Certificates.Data.Kernel.Misc.Perm23340

public section

namespace CertificateChecks.KernelMisc.K23340

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.C23340

theorem chk_true : chk23340 = true := by decide +kernel

end CertificateChecks.KernelMisc.K23340

end
