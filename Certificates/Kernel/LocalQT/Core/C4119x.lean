module

public import Certificates.Data.Kernel.LocalQT.M24L
public import Certificates.Kernel.LocalQT.Core.D4119hexE
public import Certificates.Kernel.LocalQT.Core.D4119octE1
public import Certificates.Kernel.LocalQT.Core.D4119octE2
public import Certificates.Kernel.LocalQT.Core.D4119octE3
public import Certificates.Kernel.LocalQT.Core.D4119octE4
public import Certificates.Kernel.LocalQT.Core.D4119w
public import Certificates.Kernel.LocalQT.Core.D4119img
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4119x

open CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.M24 CFSG.KD.LQT.C4119w

local notation "GL" => CFSG.KD.LQT.C4119hexE.GL

theorem x0 : x0K 24 GL xWL = true := by quickRfl
theorem sub : subK 24 GL pWL 7 1024 = true := by quickRfl

theorem xH : wordEqK 24 GL C4119hexE.nWL xN_hexE xWL = true := by quickRfl
theorem x1 : wordEqK 24 GL C4119octE1.nWL xN_octE1 xWL = true := by quickRfl
theorem x2 : wordEqK 24 GL C4119octE2.nWL xN_octE2 xWL = true := by quickRfl
theorem x3 : wordEqK 24 GL C4119octE3.nWL xN_octE3 xWL = true := by quickRfl
theorem x4 : wordEqK 24 GL C4119octE4.nWL xN_octE4 xWL = true := by quickRfl
theorem oH : wordEqK 24 GL C4119hexE.nWL omN omWL = true := by quickRfl

theorem e1 : allZ C4119octE1.eWL eN_octE1 (fun v w => wordEqK 24 GL C4119octE1.nWL w v) = true := by
  quickRfl
theorem e2 : allZ C4119octE2.eWL eN_octE2 (fun v w => wordEqK 24 GL C4119octE2.nWL w v) = true := by
  quickRfl
theorem e3 : allZ C4119octE3.eWL eN_octE3 (fun v w => wordEqK 24 GL C4119octE3.nWL w v) = true := by
  quickRfl
theorem e4 : allZ C4119octE4.eWL eN_octE4 (fun v w => wordEqK 24 GL C4119octE4.nWL w v) = true := by
  quickRfl

theorem vH : imgVK 24 (C4119hexE.eWL.map (evalWK 24 GL)) (C4119hexE.nWL.map (evalWK 24 GL))
    (evalWK 24 GL omWL) 13 = true := by quickRfl
theorem d1 : imgCK 24 (C4119octE1.eWL.map (evalWK 24 GL)) (C4119octE1.nWL.map (evalWK 24 GL))
    C4119img.C_octE1 C4119img.W_octE1 43 20160 = true := by quickRfl
theorem d2 : imgCK 24 (C4119octE2.eWL.map (evalWK 24 GL)) (C4119octE2.nWL.map (evalWK 24 GL))
    C4119img.C_octE2 C4119img.W_octE2 42 20160 = true := by quickRfl
theorem d3 : imgCK 24 (C4119octE3.eWL.map (evalWK 24 GL)) (C4119octE3.nWL.map (evalWK 24 GL))
    C4119img.C_octE3 C4119img.W_octE3 44 20160 = true := by quickRfl
theorem d4 : imgCK 24 (C4119octE4.eWL.map (evalWK 24 GL)) (C4119octE4.nWL.map (evalWK 24 GL))
    C4119img.C_octE4 C4119img.W_octE4 43 20160 = true := by quickRfl

end CFSG.KD.LQT.C4119x

end
