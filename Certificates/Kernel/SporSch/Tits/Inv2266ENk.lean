module

public import Certificates.Kernel.SporSch.Tits.Inv2266M
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 20000

namespace CertificateChecks.KernelSporSch.TitsInv

open CertificateChecks.KernelSpor

#kst_all5 CertificateChecks.KernelSporSch.TitsNkE 1755 11 24 2 TitsN.LR TitsN.TR QNk

end CertificateChecks.KernelSporSch.TitsInv

end
