module

public import Certificates.Kernel.SporSch.HN.PrimK.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def img1 (i : Nat) : Bool := imgOk (Nat.add 192 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.I1 CFSG.KD.HNXK.img1 187

end
