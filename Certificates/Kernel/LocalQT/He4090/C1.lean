module

public import Certificates.Kernel.LocalQT.He4090.L
public import Certificates.Kernel.He4049.T
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.H4090

open CFSG.KC.Enum CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.LQT.PcW

theorem canonA : canonK 8330 14 16383 116620 (CFSG.KD.LQT.C4141.TF 0) = true := by
  quickRfl

theorem bindA : allN 8330 (fun i => Nat.beq (pg 14 16383 (CFSG.KD.LQT.C4141.TF 0) i)
    (pg 14 16383 (CFSG.KD.He4049.TF 0) i)) = true := by
  quickRfl

theorem canonB : canonK 8330 14 16383 116620 (CFSG.KD.LQT.C4141.TF 1) = true := by
  quickRfl

theorem bindB : allN 8330 (fun i => Nat.beq (pg 14 16383 (CFSG.KD.LQT.C4141.TF 1) i)
    (pg 14 16383 (CFSG.KD.He4049.TF 1) i)) = true := by
  quickRfl

theorem idc : Nat.beq (pidn 8330 14) (TF 0) = true := by
  quickRfl

theorem m2 : Nat.beq (wordPB 8330 14 16383 Lab [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1]
    (TF 0)) (TF 1) = true := by
  quickRfl

theorem m7lo : Nat.beq (wordPB 8330 14 16383 Lab [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0] (TF 0))
    (TF 2) = true := by
  quickRfl

theorem m7 : Nat.beq (wordPB 8330 14 16383 Lab [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] (TF 2))
    (TF 3) = true := by
  quickRfl

end CFSG.KD.LQT.H4090

end
