module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Kernel.M24G.SextData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem sextReplay_ok : replayOK Native.keyL sextStepsF Native.baseSext 3000 SL sPar sGen
    (posTree Native.keyL SL) = true := by
  decide +kernel

end CFSG.KC.M24G
