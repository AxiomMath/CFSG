module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.NatsGen
public import Certificates.Kernel.J2Cover.ModelsAux2
meta import Certificates.Kernel.J2Cover.ModelsAux2
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelJ2Cover.MTR CFSG.ComponentClassification.J2Cover.Models.mulTab 7

#kmisc_packarrs CertificateChecks.KernelJ2Cover.DP CertificateChecks.KernelJ2Cover.decompP 7

#kmisc_packarrs CertificateChecks.KernelJ2Cover.DI CertificateChecks.KernelJ2Cover.decompI 13

#kmisc_packarrs CertificateChecks.KernelJ2Cover.YP CertificateChecks.KernelJ2Cover.ydP 7

#kmisc_packarrs CertificateChecks.KernelJ2Cover.YI CertificateChecks.KernelJ2Cover.ydI 13

#ks_perm CertificateChecks.KernelJ2Cover.CA0P 13 CFSG.ComponentClassification.J2Cover.Models.cosetAct0

#ks_perm CertificateChecks.KernelJ2Cover.CA1P 13 CFSG.ComponentClassification.J2Cover.Models.cosetAct1

#ks_perm CertificateChecks.KernelJ2Cover.CW0P 7 CFSG.ComponentClassification.J2Cover.Models.cosetWit0

#ks_perm CertificateChecks.KernelJ2Cover.CW1P 7 CFSG.ComponentClassification.J2Cover.Models.cosetWit1

#ks_perm CertificateChecks.KernelJ2Cover.SGP 13 CFSG.ComponentClassification.J2Cover.Models.sigmaT

#kmisc_packarrs CertificateChecks.KernelJ2Cover.HRP CFSG.ComponentClassification.J2Cover.Models.hRowsAll
  128

#ks_perm CertificateChecks.KernelJ2Cover.FRP 128 CFSG.ComponentClassification.J2Cover.Models.fRows

#lc_natsof CertificateChecks.KernelJ2Cover.NA0 CFSG.ComponentClassification.J2Cover.Models.cosetAct0

#lc_natsof CertificateChecks.KernelJ2Cover.NA1 CFSG.ComponentClassification.J2Cover.Models.cosetAct1

#lc_natsof CertificateChecks.KernelJ2Cover.NW0 CFSG.ComponentClassification.J2Cover.Models.cosetWit0

#lc_natsof CertificateChecks.KernelJ2Cover.NW1 CFSG.ComponentClassification.J2Cover.Models.cosetWit1

#lc_natsof CertificateChecks.KernelJ2Cover.NSG CFSG.ComponentClassification.J2Cover.Models.sigmaT

#lc_natsof CertificateChecks.KernelJ2Cover.NH0 CFSG.ComponentClassification.J2Cover.Models.hRows0

#lc_natsof CertificateChecks.KernelJ2Cover.NH1 CFSG.ComponentClassification.J2Cover.Models.hRows1

#lc_natsof CertificateChecks.KernelJ2Cover.NH2 CFSG.ComponentClassification.J2Cover.Models.hRows2

#lc_natsof CertificateChecks.KernelJ2Cover.NH3 CFSG.ComponentClassification.J2Cover.Models.hRows3

#lc_natsof CertificateChecks.KernelJ2Cover.NH4 CFSG.ComponentClassification.J2Cover.Models.hRows4

#lc_natsof CertificateChecks.KernelJ2Cover.NH5 CFSG.ComponentClassification.J2Cover.Models.hRows5

end
