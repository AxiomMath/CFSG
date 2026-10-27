module

public import Certificates.Kernel.Hall82K.SYData
public import Certificates.Kernel.Hall82K.DAData
public import Certificates.Kernel.Hall82K.EnumData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Hall82K CFSG.KD.Hall82E CFSG.KD.Hall82A

theorem ch840001syB : syBasicK EM SYI SYT = true := by decide +kernel

theorem ch840001syCl : syClK SYT SYL = true := by decide +kernel

theorem ch840001syL : syListK EM SYI DZC SYL = true := by decide +kernel

end CFSG.KD.Hall82L
