module

public import Certificates.Data.Kernel.J3Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.J3Dc

@[expose] def ch2 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 8 i)

end CFSG.KD.J3Dc

#kss_each CFSG.KD.J3Dc.G2 CFSG.KD.J3Dc.ch2 4

end
