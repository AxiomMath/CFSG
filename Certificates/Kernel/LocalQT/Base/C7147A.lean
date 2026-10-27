module

public import Certificates.Kernel.LocalQT.Base.C7147D
public import Certificates.Kernel.LocalQT.Base.C4076D
public import Certificates.Data.Kernel.LocalQT.TreeR
public import CFSG.Quasithin.Vol2.KGFactRankRuData
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

#kc_each CFSG.KD.LQT.C7147 ch7147c
  (fun k => CFSG.KC.LQT.TR.childR 15 3 16384 338 CFSG.KD.LQT.C4076.PT CFSG.KD.LQT.C4076.CT
    CFSG.Quasithin.H13.KGRank.ruRankNodes CFSG.KD.LQT.C7147.cand k) 12 13

end
