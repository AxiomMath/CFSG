module

public import Certificates.Kernel.LyBase.Words
public import CFSG.Certificates.Kernel.Common.EachTrue
import all CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

#kc_each CertificateChecks.KernelLyBase b4_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 4 j) 0 5
#kc_each CertificateChecks.KernelLyBase b5_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 5 j) 0 2
#kc_each CertificateChecks.KernelLyBase b6_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 6 j) 0 5
#kc_each CertificateChecks.KernelLyBase b7_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 7 j) 0 2
#kc_each CertificateChecks.KernelLyBase b8_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 8 j) 0 1

end
