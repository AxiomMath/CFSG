module

public import Certificates.Kernel.M3BSyl.SylData
public import Certificates.Kernel.M3BSyl.Syl2Data

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BS

open CFSG.KD.M3BS CFSG.KD.M3BS2

theorem m3bs_wv : walkChk gs v wv = true := by decide +kernel

theorem m3bs_wu : walksChk gs us wu = true := by decide +kernel

theorem m3bs_ko : ordChk wv ko = true := by decide +kernel

theorem m3bs_for : forestW gs wv wu (r3.map Prod.fst ++ r9) fr = true := by decide +kernel

end CFSG.KC.M3BS

end
