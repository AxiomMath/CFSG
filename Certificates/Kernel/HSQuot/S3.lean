module

public import Certificates.Kernel.HSQuot.D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.QuotS

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSQuot

@[expose] noncomputable def famS3 (c : Nat) : Bool :=
  CFSG.KC.LQT.QS.setQ 11 [0, 1, 2] 3 18 RT2 10752 14 E2 PG2 (Nat.mul (Nat.add c 21) 256) 256

end CFSG.KD.HSQuot

#kss_each CFSG.KD.HSQuot.S3 CFSG.KD.HSQuot.famS3 21

end
