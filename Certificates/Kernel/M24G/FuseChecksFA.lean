module

public import Certificates.Data.Kernel.M24G.FusePack
public import Certificates.Data.Kernel.M24G.FuseFast
public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Kernel.M24G.FuseData
public import Certificates.Kernel.M24G.FusePosData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G

set_option maxHeartbeats 0 in
theorem fuseOrbA_okF : replayOK (fun c => c) fuseStepsF fusePiAP 32000 FuseD.aL FuseD.aPar
    FuseD.aGen (balTree FuseS.aS) = true := by
  decide +kernel

end CFSG.KC.M24G.FuseC
