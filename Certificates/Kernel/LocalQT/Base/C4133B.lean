module

public import Certificates.Kernel.LocalQT.Base.C4133D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.X1H

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4133

@[expose] noncomputable def famB (c : Nat) : Bool :=
  CFSG.KC.LQT.XH.x1HB 1100 11 9 3 512 [G0, G1, G2] RC BO IB PT CT (Nat.mul c 32) 32

end CFSG.KD.LQT.C4133

#kss_each CFSG.KD.LQT.C4133.B CFSG.KD.LQT.C4133.famB 16

end
