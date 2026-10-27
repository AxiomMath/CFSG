module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core8 (i : Nat) : Bool := coreOk (Nat.add 16384 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C8 CFSG.KD.HNXK.core8 1429

end
