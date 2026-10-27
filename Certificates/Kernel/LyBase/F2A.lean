module

public import Certificates.Kernel.LyBase.Words
public import CFSG.Certificates.Kernel.Common.EachTrue
import all CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

#kc_each CertificateChecks.KernelLyBase b0_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 0 j) 0 4
#kc_each CertificateChecks.KernelLyBase b1_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 1 j) 0 4
#kc_each CertificateChecks.KernelLyBase b2_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 2 j) 0 1
#kc_each CertificateChecks.KernelLyBase b3_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 3 j) 0 2

end
