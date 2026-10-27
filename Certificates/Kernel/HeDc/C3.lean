module

public import Certificates.Kernel.HeDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.HeDc

@[expose] def ch3 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 18 i)

end CFSG.KD.HeDc

#kss_each CFSG.KD.HeDc.K3 CFSG.KD.HeDc.ch3 6

end
