module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.OrbData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.DeltaC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem ok : deltaCkF (lookW 3795 72 Native.key3 dec3 TL) (lookW 3795 77 (packW 11) (decW 7 11) TS)
    (fun cls => classOrbitK Native.nTrio cls [1, 42, 56, 1008, 2688]
      (trioStepsK TL (lookW 3795 72 Native.key3 dec3 TL) Native.lTabs) dRuns) = true := by
  decide +kernel

end CFSG.KC.M24G.DeltaC
