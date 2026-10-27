module

public import Certificates.Kernel.J4Q.ZFrOk
public import Certificates.Kernel.J4Q.ZFrF
import Certificates.Kernel.J4Q.VlE

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KD.J4Q CFSG.QuasithinUnique.A5

theorem chkZFr_A : chkZFr 4 (zB336T0 37) zGwB336a zfTsA zfBaseA zfTrA zfSurvA zfSqA zfDA zfEA = true :=
  chkZFr_of_parts ETCA.all (by decide) ZFA.all

theorem chkZFr_B : chkZFr 4 (zB336T0 97) zGwB336b zfTsB zfBaseB zfTrB zfSurvB zfSqB zfDB zfEB = true :=
  chkZFr_of_parts ETCA.all (by decide) ZFB.all

theorem chkZFr_C : chkZFr 4 (zB336T0 236) zGwB336c zfTsC zfBaseC zfTrC zfSurvC zfSqC zfDC zfEC = true :=
  chkZFr_of_parts ETCA.all (by decide) ZFC.all

theorem chkZFr_D : chkZFr 4 (zB336T0 491) zGwB336d zfTsD zfBaseD zfTrD zfSurvD zfSqD zfDD zfED = true :=
  chkZFr_of_parts ETCA.all (by decide) ZFD.all

end CertificateChecks.KernelJ4Q

end
