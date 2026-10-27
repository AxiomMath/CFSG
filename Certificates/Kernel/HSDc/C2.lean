module

public import Certificates.Data.Kernel.HSDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.HSDc

@[expose] def ch2 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 4 i)

end CFSG.KD.HSDc

#kss_each CFSG.KD.HSDc.K2 CFSG.KD.HSDc.ch2 2

end
