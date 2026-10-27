module

public import Certificates.Kernel.HeDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.HeDc

@[expose] def ch0 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 0 i)

end CFSG.KD.HeDc

#kss_each CFSG.KD.HeDc.K0 CFSG.KD.HeDc.ch0 6

end
