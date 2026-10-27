module

public import Certificates.Kernel.LyBase.Words
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

#kc_each CertificateChecks.KernelLyBase bfam (CertificateChecks.KernelLyBase.famFix) 0 11

namespace CertificateChecks.KernelLyBase

theorem inv_fix : invFix = true := by decide +kernel

theorem s1_fix : s1Fix = true := by decide +kernel

theorem s2_fix : s2Fix = true := by decide +kernel

theorem orb0_ok : orb0 = true := by decide +kernel

theorem orb1_ok : orb1 = true := by decide +kernel

theorem tree2_ok : tree2 = true := by decide +kernel

end CertificateChecks.KernelLyBase

end
