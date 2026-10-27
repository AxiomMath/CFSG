module

public import Certificates.Data.Kernel.HSDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.HSDc

@[expose] def ch1 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 2 i)

end CFSG.KD.HSDc

#kss_each CFSG.KD.HSDc.K1 CFSG.KD.HSDc.ch1 2

end
