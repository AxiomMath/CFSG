module

public import Certificates.Kernel.He589208.M
public import Certificates.Data.Kernel.LocalQT.BaseT
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.He589208.NA

open CFSG.KC.LQT.BT CFSG.Quasithin.H13.LocDbl.HeC0

theorem n0 : nodesT 8330 14 prog S.TF 0 8 = true := by quickRfl
theorem n1 : nodesT 8330 14 prog S.TF 8 8 = true := by quickRfl
theorem n2 : nodesT 8330 14 prog S.TF 16 8 = true := by quickRfl
theorem n3 : nodesT 8330 14 prog S.TF 24 8 = true := by quickRfl

@[expose] noncomputable def invPairs : List (Nat × Nat) :=
  [(abc 0, P.TF 0), (abc 1, P.TF 1), (rtc 0, P.TF 2), (rtc 1, P.TF 3), (rtc 2, P.TF 4)]

theorem inv_ok : invPairs.all (fun c => (List.range 8330).all fun p =>
    im c.2 (im c.1 p) == p && im c.1 (im c.2 p) == p && decide (im c.1 p < 8330) &&
      decide (im c.2 p < 8330)) = true := by
  quickRfl

end CFSG.KD.He589208.NA

end
