module

public import Certificates.Data.Kernel.RuDc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.RuDc

@[expose] def ch5 (i : Nat) : Bool := CFSG.KC.SLDc.chunkOK C D (Nat.add 837 i)

end CFSG.KD.RuDc

#kss_each CFSG.KD.RuDc.G5 CFSG.KD.RuDc.ch5 2

end
