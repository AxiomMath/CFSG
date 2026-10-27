module

public import Certificates.Kernel.M23Dc.SigmaDefs
public import CFSG.Quasithin.Background.E2TwoProofSporM23Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.M23Dc

open CFSG.Quasithin.H.MathieuLat

theorem inclB : (List.range 16).all (fun j => (List.range 16).all fun jj =>
    gK j jj == (m23Incl.getD j []).contains jj) = true := by
  quickRfl

end CFSG.KD.M23Dc

end
