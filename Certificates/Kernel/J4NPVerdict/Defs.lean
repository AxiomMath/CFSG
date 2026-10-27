module

public import Certificates.Data.Kernel.J4NPVerdict
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.QT2AData
public import Certificates.Kernel.J4Q.MaskData
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.J4NPV

#kc_repo #kc_nat_items_gz CFSG.KD.J4NPV
  "Certificates/Kernel/J4NPVerdict/data/Tabs.items.gz" 41262 16851517622876944126
  GI_[9] W1 W2 W1i W2i FM_[10]

end CFSG.KD.J4NPV

namespace CertificateChecks.KernelJ4NPV

open CFSG.KD.J4Q CFSG.KD.J4NPV

@[expose] noncomputable def vjT : CFSG.KC.J4NPV.Tabs where
  c := c
  rm := rm
  one := one
  l5 := [L0, L1, L2, A, B]
  l5i := [L0i, L1i, L2i, Ai, Bi]
  ge := [QA_0, QA_1, QA_2, QA_3, QA_4, QA_5, QA_6, QA_7, QA_8, QA_9, QA_10, QA_11, YA, YB, YP5, YP7,
    YP11, U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, mkKM_0, mkKM_1, mkKM_2, mkKM_3]
  gei := [QI_0, QI_1, QI_2, QI_3, QI_4, QI_5, QI_6, QI_7, QI_8, QI_9, QI_10, QI_11, GI_0, GI_1, GI_2,
    GI_3, GI_4, U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, GI_5, GI_6, GI_7, GI_8]
  us := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]
  km := [mkKM_0, mkKM_1, mkKM_2, mkKM_3]
  fm := [FM_0, FM_1, FM_2, FM_3, FM_4, FM_5, FM_6, FM_7, FM_8, FM_9]

end CertificateChecks.KernelJ4NPV

end
