module

public import Certificates.Kernel.HSQuot.D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.QuotS

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSQuot

@[expose] noncomputable def famS1 (c : Nat) : Bool :=
  CFSG.KC.LQT.QS.setQ 11 [0, 1, 2] 2 18 RT1 3840 12 E1 PG1 (Nat.mul c 256) 256

end CFSG.KD.HSQuot

#kss_each CFSG.KD.HSQuot.S1 CFSG.KD.HSQuot.famS1 15

end
