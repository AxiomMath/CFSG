module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort5 (i : Nat) : Bool := sortOk (Nat.add 10240 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S5 CFSG.KD.HNXK.sort5 2048

end
