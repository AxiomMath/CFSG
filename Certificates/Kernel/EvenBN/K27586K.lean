module

public import Certificates.Kernel.EvenBN.K27586D
public import Certificates.Kernel.SporSch.Tits.GenAll5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kst_all5 CertificateChecks.KernelEvenBN.NLoc.KA 1755 11 8 2 CertificateChecks.KernelSpor.TitsK.LR
  CertificateChecks.KernelSpor.TitsK.TR CertificateChecks.KernelEvenBN.NLoc.QK

end
