module

public import Certificates.Kernel.LocalQT.TwoB.C4150KF
public import Certificates.Kernel.LocalQT.TwoB.C4150K

public section

set_option maxRecDepth 400000

#kqb_range CFSG.KD.LQT.TB.HF CFSG.KD.LQT.TB.ckHF 0 23

namespace CFSG.KD.LQT.TB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.MulH

theorem ch4150hF_neg : hsortPtKF 3850 12 (mask 12) Y.cnt (fun _ => 0) Y.HS Y.HSI 0 = false := by
  decide +kernel

end CFSG.KD.LQT.TB

end
