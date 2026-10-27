module

public import Certificates.Data.Kernel.M24Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.M24Dc

@[expose] def ch2 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 4 i)

end CFSG.KD.M24Dc

#kss_each CFSG.KD.M24Dc.K2 CFSG.KD.M24Dc.ch2 2

end
