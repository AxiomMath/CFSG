module

public import Certificates.Kernel.LyBase.Words
public import CFSG.Certificates.Kernel.Common.EachTrue
import all CFSG.Sporadic.Recognition.LyonsFinalDist2Inputs

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100

public section

#kc_each CertificateChecks.KernelLyBase b9_ (fun j => CertificateChecks.KernelLyBase.stepFixChunk 9 j) 0 10

end
