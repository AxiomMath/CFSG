module

public import Certificates.Kernel.SporSch.Ru.CNG
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_schg CertificateChecks.KernelSporSch.RuNS 600 1200

end
