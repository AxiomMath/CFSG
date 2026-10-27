module

public import Certificates.Data.Kernel.M24Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.M24Dc

@[expose] def ch0 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 0 i)

end CFSG.KD.M24Dc

#kss_each CFSG.KD.M24Dc.K0 CFSG.KD.M24Dc.ch0 2

end
