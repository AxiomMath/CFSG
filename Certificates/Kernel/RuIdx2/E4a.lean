module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2

@[expose] noncomputable def fE4a (i : Nat) : Bool := famE 4 (Nat.add 0 i)

end CFSG.KD.RuIdx2

#kss_each CFSG.KD.RuIdx2.E4a CFSG.KD.RuIdx2.fE4a 12

end
