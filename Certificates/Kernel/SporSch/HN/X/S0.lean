module

public import Certificates.Kernel.SporSch.HN.X.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def sort0 (i : Nat) : Bool := sortOk (Nat.add 0 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.S0 CFSG.KD.HNXK.sort0 2048

end
