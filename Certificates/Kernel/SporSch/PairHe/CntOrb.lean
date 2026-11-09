module

public import Certificates.Kernel.SporSch.PairHe.OrbFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.orbB 0 3 8

#kss_b2 CertificateChecks.KernelSporSch.PHeCn CertificateChecks.KernelSporSch.PHeCn.permB 0 7 7

namespace CertificateChecks.KernelSporSch.PHeCn

theorem rep_ok : repB = true := by quickRfl

theorem op_ok : opB = true := by quickRfl

theorem op2_ok : opB2 = true := by quickRfl

end CertificateChecks.KernelSporSch.PHeCn

end
