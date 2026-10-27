module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcFive.E3

public section

namespace CFSG.KC.MonPcFiveD

open CFSG.KC.MonPcFive

theorem e3_0 : e3OK 0 8 = true := by quickRfl
theorem e3_1 : e3OK 8 8 = true := by quickRfl
theorem e3_2 : e3OK 16 8 = true := by quickRfl
theorem e3_3 : e3OK 24 7 = true := by quickRfl

end CFSG.KC.MonPcFiveD

end
