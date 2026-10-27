module

public import Certificates.Data.HuppertU38.Data
public meta import Certificates.Data.HuppertU38.Data
public import Certificates.Kernel.SchreierFam.C188001W
public import Certificates.Kernel.Sporadic.RawGenSchOJ

public section

namespace CertificateChecks.KernelSchreierFam.U38

@[expose] def d1 : List (List ℤ) := CFSG.RankThree.PartTwo.Sec4.Item434U38.words1.toList.drop 9

end CertificateChecks.KernelSchreierFam.U38

end

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelSchreierFam.U38C1 513 10 32 128
  CFSG.RankThree.PartTwo.Sec4.Item434U38.strong1 CFSG.RankThree.PartTwo.Sec4.Item434U38.base1 9
  CertificateChecks.KernelSchreierFam.U38.d1

#ks_rawchain_sl2_lv CertificateChecks.KernelSchreierFam.U38C1 0 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelSchreierFam.U38C1 1 0 5
#ks_rawchain_sl2_lv CertificateChecks.KernelSchreierFam.U38C1 2 0 5
#ks_rawchain_sl2_sch CertificateChecks.KernelSchreierFam.U38C1 1 0 16
#ks_rawchain_sl2_sch CertificateChecks.KernelSchreierFam.U38C1 2 0 12

#ks_rawchain_sl2_osub CertificateChecks.KernelSchreierFam.U38C1 1 6 7 8
  CertificateChecks.KernelSchreierFam.U38.ow
#ks_rawchain_sl2_scho CertificateChecks.KernelSchreierFam.U38C1 0 17

public section

#ks_rawchain_sl2_joino CertificateChecks.KernelSchreierFam.U38C1
