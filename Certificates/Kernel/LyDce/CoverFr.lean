module

public import Certificates.Kernel.LyDce.CoverData
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
set_option maxRecDepth 100000

public section

#kc_each CertificateChecks.KernelLyDce fr (fun n => CertificateChecks.KernelLyDce.frAt n) 0 4

namespace CertificateChecks.KernelLyDce

theorem cov_all : covAll = true := by decide +kernel

end CertificateChecks.KernelLyDce

end
