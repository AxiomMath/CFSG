module

public import Certificates.Kernel.LocalQT.Base.C7147D
public import Certificates.Kernel.LocalQT.Base.C4076D
public import Certificates.Data.Kernel.LocalQT.TreeR
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C7147

open CFSG.KC.LQT.TR

theorem cnd : candOK 15 3 16384 C4076.PT C4076.CT cand = true := by
  quickRfl

end CFSG.KD.LQT.C7147

end
