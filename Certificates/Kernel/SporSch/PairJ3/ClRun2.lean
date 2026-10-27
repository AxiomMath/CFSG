module

public import Certificates.Kernel.SporSch.PairJ3.ClFns
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

set_option maxRecDepth 400000

#kss_b2 CertificateChecks.KernelSporSch.PJ3Cl CertificateChecks.KernelSporSch.PJ3Cl.runB 52 78 8

end
