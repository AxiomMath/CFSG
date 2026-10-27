module

public import Certificates.Kernel.SporSch.HN.PrimK.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def img0 (i : Nat) : Bool := imgOk (Nat.add 0 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.I0 CFSG.KD.HNXK.img0 192

end
