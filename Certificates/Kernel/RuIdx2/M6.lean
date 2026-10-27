module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public section

namespace CFSG.KD.RuIdx2

@[expose] noncomputable def fM6 (i : Nat) : Bool := famM 6 i

end CFSG.KD.RuIdx2

#kss_each CFSG.KD.RuIdx2.M6 CFSG.KD.RuIdx2.fM6 27

end
