module

public import Certificates.Data.Kernel.Hall82K.ML
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_nat_items_gz CFSG.KD.Hall82L "Certificates/Kernel/Hall82K/data/hall82ml.items.gz" 23447 3556894721903570406
  MRT MZI MCW MNV MCT YC TC MYI YTE YTPA YTSG YTCT MF8

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Hall82K

@[expose] noncomputable def EY (k : Nat) : Nat := lane YTE 36 68719476735 k
@[expose] noncomputable def PY (k : Nat) : Nat := lane YTPA 32 4294967295 k
@[expose] noncomputable def SY (k : Nat) : Nat := lane YTSG 12 4095 k
@[expose] noncomputable def CY (k : Nat) : Nat := lane YTCT 12 4095 k

end CFSG.KD.Hall82L
