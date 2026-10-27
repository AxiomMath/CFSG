module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.NatsGen
public import Certificates.Kernel.J2Cover.ModelsAux
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData
meta import Certificates.Kernel.J2Cover.ModelsAux
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelJ2Cover.YT CFSG.ComponentClassification.J2Cover.Models.yArrs 9

#kmisc_packarrs CertificateChecks.KernelJ2Cover.ELT
  CFSG.ComponentClassification.J2Cover.Models.eltArrs 9

#kmisc_packarrs CertificateChecks.KernelJ2Cover.RPT
  CFSG.ComponentClassification.J2Cover.Models.repArrs 9

#ks_perm CertificateChecks.KernelJ2Cover.CPP 13 CFSG.ComponentClassification.J2Cover.Models.cosetPar

#ks_perm CertificateChecks.KernelJ2Cover.CLP 1 CFSG.ComponentClassification.J2Cover.Models.cosetLab

#ks_perm CertificateChecks.KernelJ2Cover.DPP 6 CertificateChecks.KernelJ2Cover.cosetDepth

#ks_perm CertificateChecks.KernelJ2Cover.FPP 13 CFSG.ComponentClassification.J2Cover.External.fusionP

#ks_perm CertificateChecks.KernelJ2Cover.FIP 13 CFSG.ComponentClassification.J2Cover.External.fusionI

#ks_perm CertificateChecks.KernelJ2Cover.ACP 13 CFSG.ComponentClassification.J2Cover.Models.aCoefT

#lc_natsof CertificateChecks.KernelJ2Cover.NCP CFSG.ComponentClassification.J2Cover.Models.cosetPar

#lc_natsof CertificateChecks.KernelJ2Cover.NCL CFSG.ComponentClassification.J2Cover.Models.cosetLab

#lc_natsof CertificateChecks.KernelJ2Cover.NFP CFSG.ComponentClassification.J2Cover.External.fusionP

#lc_natsof CertificateChecks.KernelJ2Cover.NFI CFSG.ComponentClassification.J2Cover.External.fusionI

#lc_natsof CertificateChecks.KernelJ2Cover.NAC CFSG.ComponentClassification.J2Cover.Models.aCoefT

end
