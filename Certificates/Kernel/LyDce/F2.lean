module

public import Certificates.Kernel.LyDce.Data
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

#kc_each CertificateChecks.KernelLyDce f (fun i => CertificateChecks.KernelLyDce.factAt i) 30 43

end
