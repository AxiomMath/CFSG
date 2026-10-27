module

public import Certificates.Kernel.SporSch.PairHe.S2Fns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHeSn CertificateChecks.KernelSporSch.PHeSn.s2B 0 8 8
#kss_b2all CertificateChecks.KernelSporSch.PHeSn CertificateChecks.KernelSporSch.PHeSn.s2B 8 8
#kss_b2 CertificateChecks.KernelSporSch.PHeSn CertificateChecks.KernelSporSch.PHeSn.srt2 0 8 8
#kss_b2all CertificateChecks.KernelSporSch.PHeSn CertificateChecks.KernelSporSch.PHeSn.srt2 8 8

namespace CertificateChecks.KernelSporSch.PHeSn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem gens : gensB = true := by quickRfl

end CertificateChecks.KernelSporSch.PHeSn

end
