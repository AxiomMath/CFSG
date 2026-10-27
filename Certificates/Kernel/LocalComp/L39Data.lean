module

public import Certificates.Kernel.LocalComp.L39Binds
public import Certificates.Kernel.LocalComp.Child3Gen
meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#lc_forest CertificateChecks.KernelLC.L39.LF 182 CFSG.EvenSmallLie.Child3.SelL39.tS [0, 91]

#lc_reps CertificateChecks.KernelLC.L39.LR 8 CFSG.EvenSmallLie.Child3.SelL39.sylowGens
  CFSG.EvenSmallLie.Child3.SelL39.repArrs

#ks_perm CertificateChecks.KernelLC.L39.LAP 7 CFSG.EvenSmallLie.Child3.SelL39.lA
#ks_perm CertificateChecks.KernelLC.L39.LBP 7 CFSG.EvenSmallLie.Child3.SelL39.lB

end
