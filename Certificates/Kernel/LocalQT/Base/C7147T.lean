module

public import Certificates.Kernel.LocalQT.Base.C7147D
public import Certificates.Kernel.LocalQT.Base.C4076D
public import Certificates.Data.Kernel.LocalQT.TreeR
public import CFSG.Quasithin.Vol2.KGFactRankRuData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C7147

open CFSG.KC.LQT.TR CFSG.Quasithin.H13.KGRank

theorem top : topR 15 3 16384 338 C4076.PT C4076.CT ruRankNodes cand 14 = true := by
  quickRfl

end CFSG.KD.LQT.C7147

#kc_each CFSG.KD.LQT.C7147 ch7147c
  (fun k => CFSG.KC.LQT.TR.childR 15 3 16384 338 CFSG.KD.LQT.C4076.PT CFSG.KD.LQT.C4076.CT
    CFSG.Quasithin.H13.KGRank.ruRankNodes CFSG.KD.LQT.C7147.cand k) 0 12

end
