module

public import Certificates.Kernel.LyDce.CoverWalkDefs
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
set_option maxRecDepth 100000

public section

#kc_each CertificateChecks.KernelLyDce wk (fun i => CertificateChecks.KernelLyDce.walkSAt i) 0 4

end
