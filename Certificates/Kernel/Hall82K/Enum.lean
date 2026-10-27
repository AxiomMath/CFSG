module

public import Certificates.Kernel.Hall82K.EnumData
public import Certificates.Data.Kernel.Hall82K.Bridge
public import CFSG.CGT.Hall82.ModelData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Hall82E

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Hall82K CFSG.CGT.Hall82

theorem ch840001enM0 : allR 0 540 enumMAt = true := by decide +kernel

theorem ch840001enM1 : allR 540 540 enumMAt = true := by decide +kernel

theorem ch840001enM2 : allR 1080 540 enumMAt = true := by decide +kernel

theorem ch840001enM3 : allR 1620 540 enumMAt = true := by decide +kernel

theorem ch840001enL : allR 0 1080 enumLAt = true := by decide +kernel

theorem ch840001enLG : zipArrK hallLGensK hallLGens = true := by decide +kernel

end CFSG.KD.Hall82E
