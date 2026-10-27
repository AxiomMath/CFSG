module

public import Certificates.Kernel.ONKLat.LatData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelONKLat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat

set_option maxRecDepth 100000

theorem ch812105t : tOK = true := by quickRfl

theorem ch812105u : uOK = true := by quickRfl

#kc_each ch812105m 0 3

theorem ch812105repM : repMOK = true := by quickRfl

theorem ch812105rep : repOK = true := by quickRfl

theorem ch812105join : joinOK = true := by quickRfl

theorem ch812105h3 : h3OK = true := by quickRfl

theorem ch812105n_ctab : notB (ctabAt m120 MG 2 TE 128 UE 315 (fun r => CR (Nat.succ r)) 0) =
    true := by quickRfl

theorem ch812105n_trans : notB (transAt m120 RC 10 TE 128 UE (fun i => UR (Nat.succ i)) 1) =
    true := by quickRfl

theorem ch812105n_clos : notB (allN 128 fun k => closedAt m120 MG 2 128 TE TC k) = true := by
  quickRfl

theorem ch812105n_repM : notB (wordAt m120 one120 MG 2 (getW repM 0) (RC 1)) = true := by
  quickRfl

theorem ch812105n_h3 : notB (wordAt m120 one120 (LG 0) 3 h3W (EL 18)) = true := by quickRfl

end CertificateChecks.KernelONKLat

end
