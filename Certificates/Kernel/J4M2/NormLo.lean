module

public import Certificates.Kernel.J4M2.NormSplit
public import Certificates.Kernel.J4M2.NormSplitCmd

public section

set_option maxRecDepth 400000

#j4m2_split CertificateChecks.KernelJ4M2.KNL CertificateChecks.KernelJ4M2.normBlk
  CertificateChecks.KernelJ4M2.nBlkA CertificateChecks.KernelJ4M2.nBlkB
  CertificateChecks.KernelJ4M2.normBlk_of 16

end
