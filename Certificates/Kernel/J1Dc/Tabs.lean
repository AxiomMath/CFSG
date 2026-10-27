module

public import Certificates.Kernel.J1Dc.Defs
public import Certificates.Kernel.Sporadic.J1K.Data
public import CFSG.Quasithin.Background.E2TwoProofSporJ1Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.J1Dc

open CFSG.KC.E64F CFSG.KS.PEnum CertificateChecks.KernelSpor.J1K
  CFSG.Quasithin.E2P.SporB.J1Lat

theorem tabsB : (List.range 1540).all (fun p => L 0 p == r32 AL p && L 1 p == r32 BE p &&
    (List.range 3).all fun i => L2 i p == wordF L (j1Words.getD i []) p) = true := by
  quickRfl

end CFSG.KD.J1Dc

end
