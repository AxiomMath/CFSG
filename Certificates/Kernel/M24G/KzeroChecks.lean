module

public import Certificates.Data.Kernel.M24G.Kzero
public import Certificates.Kernel.M24G.KzeroData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.KzeroC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

set_option maxHeartbeats 0 in
theorem kzeroSyl_ok : replayOK kzeroKeyF kzeroStepsF Native.kzeroId 1100 KzeroD.zL KzeroD.zPar
    KzeroD.zGen (posTree kzeroKeyF KzeroD.zL) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kzeroK0_ok : kzeroK0F (posTree kzeroKeyF KzeroD.zL) KzeroD.zL kzeroPairF = KzeroD.kL := by
  decide +kernel

theorem kzeroKLen_ok : KzeroD.kL.length = 64 := by
  decide +kernel

end CFSG.KC.M24G.KzeroC
