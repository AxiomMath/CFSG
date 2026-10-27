module

public import Certificates.Kernel.M3BSyl.SylData
public import Certificates.Kernel.M3BSyl.Syl2Data

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BS

open CFSG.KD.M3BS CFSG.KD.M3BS2

theorem m3bs_r3 : r3Chk gs tk cp r3 = true := by decide +kernel

theorem m3bs_r9 : r9Chk gs v r9 = true := by decide +kernel

end CFSG.KC.M3BS

end
