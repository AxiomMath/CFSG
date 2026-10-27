module

public import Certificates.Kernel.LyModel.Cp3Data
public import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false
set_option maxRecDepth 100000

public section

#kc_each CertificateChecks.KernelLyModel ly6110inv (fun i => CertificateChecks.KernelLyModel.invChunk i) 4 8

end
