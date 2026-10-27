module

public import Certificates.Kernel.SporSch.Tits.Syl8117K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 20000

namespace CertificateChecks.KernelSporSch.TitsSyl

open CertificateChecks.KernelSpor

#kst_all5 CertificateChecks.KernelSporSch.TitsSylE 1755 11 24 2 TitsN.LR TitsN.TR QSyl

end CertificateChecks.KernelSporSch.TitsSyl

end
