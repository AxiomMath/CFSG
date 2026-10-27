module

public import Certificates.Data.Kernel.Stroth77.NonSplitK

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Stroth77NS

open CFSG.CGT.Stroth77.Core CFSG.KC.Stroth77NS

theorem ch778705_rel : ∀ j, evalW sw (rel j) = 1 := by decide +kernel

theorem ch778705_cyc : cycOKt = true := by decide +kernel

theorem ch778705_g : gSpec := by decide +kernel

theorem ch778705_tits : titsSpec := by decide +kernel

theorem ch778705_cert : certOKi = true := by decide +kernel

end CFSG.KD.Stroth77NS

end
