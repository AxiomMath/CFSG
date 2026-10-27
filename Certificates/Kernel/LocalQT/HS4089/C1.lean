module

public import Certificates.Kernel.LocalQT.HS4089.L
public import Certificates.Kernel.VecCert.HS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHSLitData
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LocalQT.PcOm

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.H4089

open CFSG.KC.Enum CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.LQT.PcW CFSG.KC.LQT.PcOm CFSG.KC.VecK
open CertificateChecks.KernelVec.HS (AT BT)
open CFSG.QuasithinUnique.Vol2Native.L239.HSPairs (hsW1 hsOm1)

theorem canonA : canonK 1100 11 2047 12100 (CFSG.KD.LQT.H4089S.TF 0) = true := by
  quickRfl

theorem bindA : allN 1100 (fun i => Nat.beq (pg 11 2047 (CFSG.KD.LQT.H4089S.TF 0) i) (lk AT 32 i)) =
    true := by
  quickRfl

theorem canonB : canonK 1100 11 2047 12100 (CFSG.KD.LQT.H4089S.TF 1) = true := by
  quickRfl

theorem bindB : allN 1100 (fun i => Nat.beq (pg 11 2047 (CFSG.KD.LQT.H4089S.TF 1) i) (lk BT 32 i)) =
    true := by
  quickRfl

theorem idc : Nat.beq (pidn 1100 11) (TF 0) = true := by
  quickRfl

theorem m1 : Nat.beq (wordPB 1100 11 2047 Lab hsW1 (TF 0)) (TF 1) = true := by
  quickRfl

theorem b1t : Nat.beq (qtW 1100 11 2047 (TF 0) L1c [3, 3] 1) (TF 3) = true := by quickRfl
theorem b1i : Nat.beq (powS 1100 11 2047 (TF 0) (TF 3) 2) (TF 4) = true := by quickRfl
theorem b1n : neB (TF 3) (TF 0) = true := by quickRfl
theorem b1o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 3) 3) (TF 0) = true := by quickRfl

theorem x1t : Nat.beq (qtW 1100 11 2047 (TF 0) L1c [0] 1) (TF 5) = true := by quickRfl
theorem x1o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 5) 2) (TF 0) = true := by quickRfl
theorem x1i : Nat.beq (powS 1100 11 2047 (TF 0) (TF 5) 1) (TF 6) = true := by quickRfl
theorem x1l : labsK 1100 11 2047 (TF 5) hsOm1.lbl.toList = true := by quickRfl

theorem y1t : Nat.beq (qtW 1100 11 2047 (TF 0) L1c [2, 0, 2] 1) (TF 7) = true := by quickRfl
theorem y1o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 7) 2) (TF 0) = true := by quickRfl
theorem y1i : Nat.beq (powS 1100 11 2047 (TF 0) (TF 7) 1) (TF 8) = true := by quickRfl
theorem y1l : labsK 1100 11 2047 (TF 7) hsOm1.lbl.toList = true := by quickRfl

theorem c1a : Nat.beq (commS 1100 11 2047 (TF 5) (TF 3) (TF 6) (TF 4)) (TF 9) = true := by
  quickRfl
theorem c1b : Nat.beq (commS 1100 11 2047 (TF 7) (TF 3) (TF 8) (TF 4)) (TF 10) = true := by
  quickRfl
theorem c1n : neB (pcS 1100 11 2047 (TF 9) (TF 10)) (pcS 1100 11 2047 (TF 10) (TF 9)) = true := by
  quickRfl

theorem p1t : Nat.beq (qtW 1100 11 2047 (TF 0) L1c [3, 1, 2, 1] 2) (TF 11) = true := by quickRfl
theorem p1n : neB (TF 11) (TF 0) = true := by quickRfl
theorem p1o : Nat.beq (powS 1100 11 2047 (TF 0) (TF 11) 5) (TF 0) = true := by quickRfl
theorem p1c : neB (pcS 1100 11 2047 (TF 5) (TF 11)) (pcS 1100 11 2047 (TF 11) (TF 5)) = true := by
  quickRfl

theorem om1 : omK 1100 11 2047 L1c 4 15 hsOm1.lbl.toList (hsOm1.pn.toList.map Array.toList) =
    true := by
  quickRfl

theorem tree1 : ∀ i < 15, 0 < i → hsOm1.par[i]! < i ∧ hsOm1.via[i]! < 4 ∧
    (hsOm1.pn[hsOm1.via[i]!]!)[hsOm1.par[i]!]! = i := by
  decide +kernel

theorem nodup1 : hsOm1.lbl.toList.Nodup := by
  decide +kernel

end CFSG.KD.LQT.H4089

end
