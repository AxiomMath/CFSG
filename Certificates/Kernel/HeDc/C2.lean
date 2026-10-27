module

public import Certificates.Kernel.HeDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.HeDc

@[expose] def ch2 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 12 i)

end CFSG.KD.HeDc

#kss_each CFSG.KD.HeDc.K2 CFSG.KD.HeDc.ch2 6

end
