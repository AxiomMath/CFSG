module

public import Certificates.Kernel.SporSch.PairHe.ClFns
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PHeCl CertificateChecks.KernelSporSch.PHeCl.runB 96 128 8

end
