module

public import Certificates.Kernel.Fi22Rho.Data
public import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option maxRecDepth 400000

#kon_slices CertificateChecks.KernelFi22Rho.nodeSl 0 54
#kon_join CertificateChecks.KernelFi22Rho.nodeAll CertificateChecks.KernelFi22Rho.nodeSl 54

#kon_slices CertificateChecks.KernelFi22Rho.relSl 0 288
#kon_join CertificateChecks.KernelFi22Rho.relAll CertificateChecks.KernelFi22Rho.relSl 288

end
