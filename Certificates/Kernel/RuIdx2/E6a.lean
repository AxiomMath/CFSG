module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2

@[expose] noncomputable def fE6a (i : Nat) : Bool := famE 6 (Nat.add 0 i)

end CFSG.KD.RuIdx2

#kss_each CFSG.KD.RuIdx2.E6a CFSG.KD.RuIdx2.fE6a 12

end
