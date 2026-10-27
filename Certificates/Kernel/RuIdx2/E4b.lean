module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2

@[expose] noncomputable def fE4b (i : Nat) : Bool := famE 4 (Nat.add 12 i)

end CFSG.KD.RuIdx2

#kss_each CFSG.KD.RuIdx2.E4b CFSG.KD.RuIdx2.fE4b 12

end
