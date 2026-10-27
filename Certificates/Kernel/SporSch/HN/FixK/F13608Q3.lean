module

public import Certificates.Kernel.SporSch.HN.FixK.Tab13608
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix13608_3 (i : Nat) : Bool := fix13608 (Nat.add 3 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F13608_3 CFSG.KD.HNXK.fix13608_3 1

end
