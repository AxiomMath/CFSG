module

public import Certificates.Kernel.Multipliers.U43Cone
public import CFSG.Certificates.Kernel.Bounds.U62Alt.Data.C_Sel
public import CFSG.Certificates.Kernel.Bounds.U62Alt.Checks.C_H
public import CFSG.Certificates.Kernel.Bounds.U62Alt.Checks.C_W
public import CFSG.Certificates.Kernel.Bounds.U62Alt.Checks.C_L

public section

namespace CertificateChecks.KernelU62

#kc_join_range Cfacts CertificateChecks.KernelCo2.runFacts_append CFSG.KD.U52C "sW" 0 12
#kc_join_range Clab CertificateChecks.KernelU43.runLabZ_append CFSG.KD.U52C "sL" 0 12
#kc_join_range Cids CertificateChecks.KernelU43.runIds_append CFSG.KD.U52C "sI" 0 12

end CertificateChecks.KernelU62

end
