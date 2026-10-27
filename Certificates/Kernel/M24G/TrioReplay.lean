module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Kernel.M24G.TrioData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem trioReplay_ok : replayOK Native.key3 trioStepsF Native.baseTrio 5000 TL tPar tGen
    (posTree Native.key3 TL) = true := by
  decide +kernel

end CFSG.KC.M24G
