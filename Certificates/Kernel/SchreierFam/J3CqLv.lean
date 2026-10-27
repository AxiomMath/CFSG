module

public import Certificates.Kernel.SchreierFam.J3Cq
public import Certificates.Kernel.Sporadic.RawGenSplitQ

set_option maxRecDepth 400000

set_option Elab.async false

#ks_rawchain_sl2_lvq CertificateChecks.KernelSchreierFam.J3Cq.SY 0 0 8 1
#ks_rawchain_sl2_lvp CertificateChecks.KernelSchreierFam.J3Cq.SY 0 8 1283
#ks_rawchain_sl2_lvp CertificateChecks.KernelSchreierFam.J3Cq.SY 1 0 1283
#ks_rawchain_sl2_lvp CertificateChecks.KernelSchreierFam.J3Cq.SY 2 0 1283
#ks_rawchain_sl2_join CertificateChecks.KernelSchreierFam.J3Cq.SY
