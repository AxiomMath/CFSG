module

public import Certificates.Kernel.LocalQT.Base.C4076D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.FusionS

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4076

@[expose] noncomputable def famC (c : Nat) : Bool :=
  CFSG.KC.LQT.FS.fusC 15 3 16384 338 PT CT (Nat.mul c 1024) 1024

end CFSG.KD.LQT.C4076

#kss_each CFSG.KD.LQT.C4076.C CFSG.KD.LQT.C4076.famC 16

end
