module

public import Certificates.Data.Kernel.M24Dc.E64Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.M24Dc

@[expose] def e64M0 (i : Nat) : Bool := e64M (Nat.add 0 i)

end CFSG.KD.M24Dc

#kss_each CFSG.KD.M24Dc.E64C0 CFSG.KD.M24Dc.e64M0 1

end
