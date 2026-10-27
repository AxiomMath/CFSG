module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core0 (i : Nat) : Bool := coreOk (Nat.add 0 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C0 CFSG.KD.HNXK.core0 2048

end
