module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core4 (i : Nat) : Bool := coreOk (Nat.add 8192 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C4 CFSG.KD.HNXK.core4 2048

end
