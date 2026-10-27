module

public import Certificates.Kernel.SporSch.HN.PrimK.Tab
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def orb0 (i : Nat) : Bool := orbOk (Nat.add 0 i)

@[expose] def eq0 (i : Nat) : Bool := eqOk (Nat.add 0 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.O0 CFSG.KD.HNXK.orb0 192
#kss_each CFSG.KD.HNXK.A0 CFSG.KD.HNXK.eq0 192

end
