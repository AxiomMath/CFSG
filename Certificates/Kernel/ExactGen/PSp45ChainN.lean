module

public import Certificates.Kernel.ExactGen.PSp45Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#ks_rawchain CertificateChecks.KernelEG.PSp45.CN 156 8 16 CertificateChecks.KernelEG.PSp45.sN
  CertificateChecks.KernelEG.PSp45.bN 3 CertificateChecks.KernelEG.PSp45.DN
