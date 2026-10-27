module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort2 (i : Nat) : Bool := sortOk (Nat.add 4096 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S2 CFSG.KD.HNXK.sort2 2048

end
