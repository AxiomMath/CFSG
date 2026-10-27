module

public import Certificates.Kernel.LocalQT.Pairs.C4093h
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4093

@[expose] noncomputable def famCl (j : Nat) : Bool :=
  CFSG.KC.LQT.L.chainChunk 12 CFSG.KD.LQT.M12Chain.C clP j

end CFSG.KD.LQT.C4093

#kss_each CFSG.KD.LQT.C4093.Cl CFSG.KD.LQT.C4093.famCl 12

end
