module

public import Certificates.Kernel.LyDce.ChainData
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

#kc_each CertificateChecks.KernelLyDce ch (fun n => CertificateChecks.KernelLyDce.chainAt n) 0 4

namespace CertificateChecks.KernelLyDce

open CFSG.KC.LyDce

theorem gens_ok : gensOK sG = true := by decide +kernel

end CertificateChecks.KernelLyDce

end
