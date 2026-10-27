module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort6 (i : Nat) : Bool := sortOk (Nat.add 12288 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S6 CFSG.KD.HNXK.sort6 2048

end
