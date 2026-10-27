module

public import Certificates.Kernel.LocalQT.Pairs.C4093h
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4093

@[expose] noncomputable def famP1 (j : Nat) : Bool :=
  CFSG.KC.LQT.L.chainChunk 12 CFSG.KD.LQT.M12Chain.C cp1 j

end CFSG.KD.LQT.C4093

#kss_each CFSG.KD.LQT.C4093.P1 CFSG.KD.LQT.C4093.famP1 12

end
