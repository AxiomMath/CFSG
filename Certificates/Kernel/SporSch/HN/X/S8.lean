module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort8 (i : Nat) : Bool := sortOk (Nat.add 16384 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S8 CFSG.KD.HNXK.sort8 1429

end
