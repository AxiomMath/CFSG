module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort1 (i : Nat) : Bool := sortOk (Nat.add 2048 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S1 CFSG.KD.HNXK.sort1 2048

end
