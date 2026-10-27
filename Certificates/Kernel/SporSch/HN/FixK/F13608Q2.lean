module

public import Certificates.Kernel.SporSch.HN.FixK.Tab13608
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix13608_2 (i : Nat) : Bool := fix13608 (Nat.add 2 i)

end CFSG.KD.HNXK

#kss_each CFSG.KD.HNXK.F13608_2 CFSG.KD.HNXK.fix13608_2 1

end
