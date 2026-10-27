module

public import Certificates.Data.Kernel.J3Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.J3Dc

@[expose] def ch3 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 12 i)

end CFSG.KD.J3Dc

#kss_each CFSG.KD.J3Dc.G3 CFSG.KD.J3Dc.ch3 5

end
