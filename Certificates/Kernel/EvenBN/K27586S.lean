module

public import Certificates.Kernel.EvenBN.K27586D
public import Certificates.Kernel.SporSch.Tits.GenAll5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kst_all5 CertificateChecks.KernelEvenBN.NLoc.SA 1755 11 8 2 CertificateChecks.KernelSpor.TitsS.LR
  CertificateChecks.KernelSpor.TitsS.TR CertificateChecks.KernelEvenBN.NLoc.QS

end
