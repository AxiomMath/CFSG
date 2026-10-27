module

public import Certificates.Kernel.ExactGen.PSp45Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_rawchain CertificateChecks.KernelEG.PSp45.CP 156 8 16 CertificateChecks.KernelEG.PSp45.sP
  CertificateChecks.KernelEG.PSp45.bP 2 CertificateChecks.KernelEG.PSp45.DP
