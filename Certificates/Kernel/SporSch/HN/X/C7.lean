module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core7 (i : Nat) : Bool := coreOk (Nat.add 14336 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C7 CFSG.KD.HNXK.core7 2048

end
