module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort4 (i : Nat) : Bool := sortOk (Nat.add 8192 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S4 CFSG.KD.HNXK.sort4 2048

end
