module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core2 (i : Nat) : Bool := coreOk (Nat.add 4096 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C2 CFSG.KD.HNXK.core2 2048

end
