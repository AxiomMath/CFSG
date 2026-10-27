module

public import Init
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CertificateChecks.KernelOm2.BD "Certificates/Kernel/Om2K/data/tabs.items.gz" 378337 15247758994990004939
  KGb[8] LhGb[73] LhIb[73] LhWb[73] LcGb[31] LcIb[31] LcWb[31] NGb[409] NPb[409] NFb[409]
  OAb[24] OBb[24] OPb[24] SGb[8] ZTb[4]
#kc_repo #kc_nat_items_gz CertificateChecks.KernelOm2.BD "Certificates/Kernel/Om2K/data/wit.items.gz" 43341 14324367172486699211
  W0b[4096] W1b[27]
#kc_repo #kc_nat_items_gz CertificateChecks.KernelOm2.BD "Certificates/Kernel/Om2K/data/q8.items.gz" 734442 15326502310128520468
  SQ0b[4096] RT0b[240] PR0b[240] SQ2b[1024] RT2b[48] PR2b[48]
#kc_repo #kc_nat_items_gz CertificateChecks.KernelOm2.BD "Certificates/Kernel/Om2K/data/orb.items.gz" 26152 14034941792927059611
  ODb[576] CRb[4608]

#kc_select CertificateChecks.KernelOm2.BD KG KGb 8
#kc_select CertificateChecks.KernelOm2.BD LhG LhGb 73
#kc_select CertificateChecks.KernelOm2.BD LhI LhIb 73
#kc_select CertificateChecks.KernelOm2.BD LhW LhWb 73
#kc_select CertificateChecks.KernelOm2.BD LcG LcGb 31
#kc_select CertificateChecks.KernelOm2.BD LcI LcIb 31
#kc_select CertificateChecks.KernelOm2.BD LcW LcWb 31
#kc_select CertificateChecks.KernelOm2.BD NG NGb 409
#kc_select CertificateChecks.KernelOm2.BD NP NPb 409
#kc_select CertificateChecks.KernelOm2.BD NF NFb 409
#kc_select CertificateChecks.KernelOm2.BD OA OAb 24
#kc_select CertificateChecks.KernelOm2.BD OB OBb 24
#kc_select CertificateChecks.KernelOm2.BD OP OPb 24
#kc_select CertificateChecks.KernelOm2.BD SG SGb 8
#kc_select CertificateChecks.KernelOm2.BD ZT ZTb 4
#kc_select CertificateChecks.KernelOm2.BD W0 W0b 4096
#kc_select CertificateChecks.KernelOm2.BD W1 W1b 27
#kc_select CertificateChecks.KernelOm2.BD SQ0 SQ0b 4096
#kc_select CertificateChecks.KernelOm2.BD RT0 RT0b 240
#kc_select CertificateChecks.KernelOm2.BD PR0 PR0b 240
#kc_select CertificateChecks.KernelOm2.BD SQ2 SQ2b 1024
#kc_select CertificateChecks.KernelOm2.BD RT2 RT2b 48
#kc_select CertificateChecks.KernelOm2.BD PR2 PR2b 48
#kc_select CertificateChecks.KernelOm2.BD OD ODb 576
#kc_select CertificateChecks.KernelOm2.BD CR CRb 4608

public section

namespace CertificateChecks.KernelOm2.BD

@[expose] def nN : Nat := 409

@[expose] def nR0 : Nat := 240

@[expose] def nR2 : Nat := 48

end CertificateChecks.KernelOm2.BD

end
