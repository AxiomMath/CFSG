module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core5 (i : Nat) : Bool := coreOk (Nat.add 10240 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C5 CFSG.KD.HNXK.core5 2048

end
