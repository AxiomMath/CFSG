module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2

@[expose] noncomputable def fE1a (i : Nat) : Bool := famE 1 (Nat.add 0 i)

end CFSG.KD.RuIdx2

#kss_each CFSG.KD.RuIdx2.E1a CFSG.KD.RuIdx2.fE1a 13

end
