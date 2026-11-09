module

public import Certificates.Kernel.J4M2.NormSplit
public import Certificates.Kernel.J4M2.NormSplitCmd

public section

set_option maxRecDepth 400000

#j4m2_split CertificateChecks.KernelJ4M2.KNH CertificateChecks.KernelJ4M2.normBlkHi
  CertificateChecks.KernelJ4M2.nBlkHiA CertificateChecks.KernelJ4M2.nBlkHiB
  CertificateChecks.KernelJ4M2.normBlkHi_of 16

end
