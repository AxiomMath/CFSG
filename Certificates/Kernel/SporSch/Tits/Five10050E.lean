module

public import Certificates.Kernel.SporSch.Tits.Five10050D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelSporSch.TitsFive

open CertificateChecks.KernelSpor

#kst_all5 CertificateChecks.KernelSporSch.TitsHFE 1755 11 10 8 TitsH.LR TitsH.TR QFH

end CertificateChecks.KernelSporSch.TitsFive

end
