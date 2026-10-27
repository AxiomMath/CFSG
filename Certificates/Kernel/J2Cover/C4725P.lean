module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.LocalComp.NatsGen
public import Certificates.Kernel.J2Cover.C4725Aux
meta import Certificates.Kernel.J2Cover.C4725Aux

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelJ2Cover.C4725P.PSI 12
  CFSG.RankThree.PartTwo.J2Residue.C4725.psiData

#ks_perm CertificateChecks.KernelJ2Cover.C4725P.KC 14
  CFSG.RankThree.PartTwo.J2Residue.C4725.keptCodes

#ks_perm CertificateChecks.KernelJ2Cover.C4725P.TM 13
  CFSG.RankThree.PartTwo.J2Residue.C4725.tMaskAll

#ks_perm CertificateChecks.KernelJ2Cover.C4725P.KT 13 CertificateChecks.KernelJ2Cover.keptFlat

#lc_natsof CertificateChecks.KernelJ2Cover.C4725P.NPSI
  CFSG.RankThree.PartTwo.J2Residue.C4725.psiData

#lc_natsof CertificateChecks.KernelJ2Cover.C4725P.NKC
  CFSG.RankThree.PartTwo.J2Residue.C4725.keptCodes

#lc_natsof CertificateChecks.KernelJ2Cover.C4725P.NTM
  CFSG.RankThree.PartTwo.J2Residue.C4725.tMaskAll

end
