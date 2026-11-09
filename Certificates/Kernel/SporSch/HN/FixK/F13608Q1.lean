module

public import Certificates.Kernel.SporSch.HN.FixK.Tab13608
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Kernel.SporSch.HN.FixK.SplitAuto

public noncomputable section

namespace CFSG.KD.HNXK

@[expose] def fix13608_1 (i : Nat) : Bool := fix13608 (Nat.add 1 i)

end CFSG.KD.HNXK

#kss_fix_auto CFSG.KD.HNXK.F13608_1 CFSG.KD.HNXK.fix13608_1 CFSG.KD.HN13608.GE
  CFSG.KD.HNXK.FIX13608 0 1 1

end
