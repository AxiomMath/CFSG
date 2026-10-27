module

public import Certificates.Kernel.LocalQT.Base.C4133D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.X1H

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4133

@[expose] noncomputable def famS (c : Nat) : Bool :=
  CFSG.KC.LQT.XH.x1HS 9 3 512 PT CT Z1L Z2L Z3L QcL (Nat.mul c 64) 64

end CFSG.KD.LQT.C4133

#kss_each CFSG.KD.LQT.C4133.S CFSG.KD.LQT.C4133.famS 8

end
