module

public import Certificates.Kernel.SporSch.Ru.SCRData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuQS 0 0 10
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuQS 1 0 10
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuQS 2 0 10
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuQS 3 0 10
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuQS 0 0 40
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuQS 1 0 32
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuQS 2 0 6
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuQS 3 0 1
#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.RuQS

#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuBC 0 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuBC 1 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuBC 2 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuBC 0 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuBC 1 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuBC 2 0 2
#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.RuBC

#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuBN 0 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuBN 1 0 1
#ks_rawchain_sl2_lv CertificateChecks.KernelSporSch.RuBN 2 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuBN 0 0 4
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuBN 1 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelSporSch.RuBN 2 0 2
#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.RuBN

end
