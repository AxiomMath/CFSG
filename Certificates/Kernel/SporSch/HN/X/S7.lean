module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort7 (i : Nat) : Bool := sortOk (Nat.add 14336 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S7 CFSG.KD.HNXK.sort7 2048

end
