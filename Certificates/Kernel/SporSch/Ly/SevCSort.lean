module

public import Certificates.Kernel.SporSch.Ly.SevCRun0
public import Certificates.Kernel.SporSch.Ly.SevCRun1
public import Certificates.Kernel.SporSch.Ly.SevCRun2
public import Certificates.Kernel.SporSch.Ly.SevCRun3

public section

set_option maxRecDepth 400000

#kly_chain CertificateChecks.KernelSporSch.LySc so CertificateChecks.KernelSporSch.LySc.soQ 50 32

#kly_chainJoin CertificateChecks.KernelSporSch.LySc cr CertificateChecks.KernelSporSch.LySc.crQ 398 32

end
