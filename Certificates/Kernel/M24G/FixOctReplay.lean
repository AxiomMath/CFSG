module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.FixOct
public import Certificates.Kernel.M24G.FixOctData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FixOctC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

set_option maxHeartbeats 0 in
theorem fixOctReplay_ok : replayOK tabKeyF fixOctStepsF Native.fixOctIdTab 11000 FixOctD.FL
    FixOctD.fPar FixOctD.fGen (posTree tabKeyF FixOctD.FL) = true := by
  decide +kernel

theorem fixOctLen_ok : 10752 ≤ FixOctD.FL.length := by
  decide +kernel

theorem fixOctComm_ok : fixOctCommF = true := by
  decide +kernel

end CFSG.KC.M24G.FixOctC
