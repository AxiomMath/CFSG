module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def core3 (i : Nat) : Bool := coreOk (Nat.add 6144 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.C3 CFSG.KD.HNXK.core3 2048

end
