module

public import Certificates.Kernel.RuIdx2.Defs
import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

#kss_each CFSG.KD.RuIdx2.W CFSG.KD.RuIdx2.famW 7
#kss_each CFSG.KD.RuIdx2.I CFSG.KD.RuIdx2.famI 10
#kss_each CFSG.KD.RuIdx2.Q CFSG.KD.RuIdx2.famQ 4

namespace CFSG.KD.RuIdx2

theorem one : Nat.beq (psi (nat_lit 16)) (nat_lit 0) = true := by quickRfl

end CFSG.KD.RuIdx2

end
