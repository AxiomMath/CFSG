module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core1 (i : Nat) : Bool := coreOk (Nat.add 2048 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C1 CFSG.KD.HNXK.core1 2048

end
