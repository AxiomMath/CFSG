module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2

@[expose] noncomputable def fE2b (i : Nat) : Bool := famE 2 (Nat.add 13 i)

end CFSG.KD.RuIdx2

#kss_each CFSG.KD.RuIdx2.E2b CFSG.KD.RuIdx2.fE2b 13

end
