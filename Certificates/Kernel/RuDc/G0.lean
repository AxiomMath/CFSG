module

public import Certificates.Data.Kernel.RuDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.RuDc

@[expose] def ch0 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 0 i)

end CFSG.KD.RuDc

#kss_each CFSG.KD.RuDc.G0 CFSG.KD.RuDc.ch0 388

end
