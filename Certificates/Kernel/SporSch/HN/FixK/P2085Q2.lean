module

public import Certificates.Kernel.SporSch.HN.FixK.Tab2085
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix2085_2 (i : Nat) : Bool := fix2085 (Nat.add 4 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F2085_2 CFSG.KD.HNXK.fix2085_2 2

end
