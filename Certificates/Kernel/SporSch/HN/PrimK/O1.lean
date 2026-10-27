module

public import Certificates.Kernel.SporSch.HN.PrimK.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def orb1 (i : Nat) : Bool := orbOk (Nat.add 192 i)

@[expose] def eq1 (i : Nat) : Bool := eqOk (Nat.add 192 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.O1 CFSG.KD.HNXK.orb1 187
#kss_each CFSG.KD.HNXK.A1 CFSG.KD.HNXK.eq1 187

end
