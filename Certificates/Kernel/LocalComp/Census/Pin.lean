module

public import Certificates.Kernel.LocalComp.Census.Data
public meta import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Kernel.SporSch.Ru.RowsGen

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelLC.CensusS CertificateChecks.KernelLC.CensusD.slC 48
#kss_each CertificateChecks.KernelLC.CensusR CertificateChecks.KernelLC.CensusD.srC 10

end
