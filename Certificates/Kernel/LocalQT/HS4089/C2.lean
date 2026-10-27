module

public import Certificates.Kernel.LocalQT.HS4089.L
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSLitData
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LocalQT.PcOm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.H4089

open CFSG.KC.Enum CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.LQT.PcW CFSG.KC.LQT.PcOm
open CFSG.QuasithinUnique.Vol2Native.L239.HSPairs (hsW2 hsOm2)

theorem m2 : Nat.beq (wordPB 1100 11 2047 Lab hsW2 (TF 0)) (TF 2) = true := by
  quickRfl

theorem b2t : Nat.beq (qtW 1100 11 2047 (TF 0) L2c [3, 3, 1] 2) (TF 12) = true := by quickRfl
theorem b2i : Nat.beq (powS 1100 11 2047 (TF 0) (TF 12) 2) (TF 13) = true := by quickRfl
theorem b2n : neB (TF 12) (TF 0) = true := by quickRfl
theorem b2o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 12) 3) (TF 0) = true := by quickRfl

theorem x2t : Nat.beq (qtW 1100 11 2047 (TF 0) L2c [2, 1, 0, 1] 1) (TF 14) = true := by quickRfl
theorem x2o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 14) 4) (TF 0) = true := by quickRfl
theorem x2i : Nat.beq (powS 1100 11 2047 (TF 0) (TF 14) 3) (TF 15) = true := by quickRfl
theorem x2l : labsK 1100 11 2047 (TF 14) hsOm2.lbl.toList = true := by quickRfl

theorem y2t : Nat.beq (qtW 1100 11 2047 (TF 0) L2c [2, 2] 1) (TF 16) = true := by quickRfl
theorem y2o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 16) 2) (TF 0) = true := by quickRfl
theorem y2i : Nat.beq (powS 1100 11 2047 (TF 0) (TF 16) 1) (TF 17) = true := by quickRfl
theorem y2l : labsK 1100 11 2047 (TF 16) hsOm2.lbl.toList = true := by quickRfl

theorem c2a : Nat.beq (commS 1100 11 2047 (TF 14) (TF 12) (TF 15) (TF 13)) (TF 18) = true := by
  quickRfl
theorem c2b : Nat.beq (commS 1100 11 2047 (TF 16) (TF 12) (TF 17) (TF 13)) (TF 19) = true := by
  quickRfl
theorem c2n : neB (pcS 1100 11 2047 (TF 18) (TF 18)) (TF 0) = true := by quickRfl

theorem p2t : Nat.beq (qtW 1100 11 2047 (TF 0) L2c [3] 1) (TF 20) = true := by quickRfl
theorem p2n : neB (TF 20) (TF 0) = true := by quickRfl
theorem p2o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 20) 7) (TF 0) = true := by quickRfl
theorem p2c : neB (pcS 1100 11 2047 (TF 16) (TF 20)) (pcS 1100 11 2047 (TF 20) (TF 16)) = true := by
  quickRfl

theorem om2 : omK 1100 11 2047 L2c 4 21 hsOm2.lbl.toList (hsOm2.pn.toList.map Array.toList) =
    true := by
  quickRfl

theorem tree2 : ∀ i < 21, 0 < i → hsOm2.par[i]! < i ∧ hsOm2.via[i]! < 4 ∧
    (hsOm2.pn[hsOm2.via[i]!]!)[hsOm2.par[i]!]! = i := by
  decide +kernel

theorem nodup2 : hsOm2.lbl.toList.Nodup := by
  decide +kernel

end CFSG.KD.LQT.H4089

end
