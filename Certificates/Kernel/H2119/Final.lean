module

public import CFSG.Certificates.Kernel.Hering2119KSound
import Certificates.Kernel.H2119.Checks

public section

namespace CertificateChecks.KD.H2119

theorem item2119EndShareK_holds : CFSG.RankThree.PartTwo.Sec21.Hering2119S.Item2119EndShareK :=
  CFSG.KC.H2119.kfact_of_checks ch522001_n1 ch522001_n2 ch522001_n3 ch522001_l1 ch522001_l2
    ch522001_l3 ch522001_c ch522001_w01 ch522001_w02 ch522001_w03 ch522001_w11 ch522001_w12
    ch522001_w13 ch522001_k0 ch522001_k1

end CertificateChecks.KD.H2119
