module

public import Certificates.Data.Kernel.Misc.A6C5Cent

public section

namespace CFSG.KD.A6C5

open CFSG.KC.A6C5

theorem basic_ok : basic = true := by decide +kernel

theorem candA0 : candA 0 = true := by decide +kernel

theorem candA1 : candA 1 = true := by decide +kernel

theorem candA2 : candA 2 = true := by decide +kernel

end CFSG.KD.A6C5
