module

public import Certificates.Data.E27.Fi22S0
import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi22S0.OS CFSG.Sporadic.Fi22.S0.opsStr

#ks_chars CertificateChecks.KernelFi22S0.PS CFSG.Sporadic.Fi22.S0.parStr

#ks_chars CertificateChecks.KernelFi22S0.LS CFSG.Sporadic.Fi22.S0.LStr

end
