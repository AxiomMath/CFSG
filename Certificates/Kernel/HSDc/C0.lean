module

public import Certificates.Data.Kernel.HSDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.HSDc

@[expose] def ch0 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 0 i)

end CFSG.KD.HSDc

#kss_each CFSG.KD.HSDc.K0 CFSG.KD.HSDc.ch0 2

end
