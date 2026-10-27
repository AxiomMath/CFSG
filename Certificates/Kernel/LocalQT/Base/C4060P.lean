module

public import Certificates.Kernel.LocalQT.Base.C4060D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.RankB

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4060

@[expose] noncomputable def fam (j : Nat) : Bool :=
  CFSG.KC.LQT.RB.rankBP 9 3 512 PT CT 3 10 (Nat.mul j 1) 1

end CFSG.KD.LQT.C4060

#kss_each CFSG.KD.LQT.C4060.P CFSG.KD.LQT.C4060.fam 87

end
