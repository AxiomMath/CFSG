module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.HN.PcFiveE3
public import Certificates.Kernel.BabyMonster.PcFive.Data
public import Certificates.Kernel.HN.PcFive.Data

public section

namespace CFSG.KC.HN.PcFiveD

open CFSG.KC.BM.PcFive CFSG.KC.HN.PcFive

theorem te3 : e3OK CFSG.KC.BM.PcFiveD.rep ea eb 152 = true := by quickRfl

end CFSG.KC.HN.PcFiveD

end
