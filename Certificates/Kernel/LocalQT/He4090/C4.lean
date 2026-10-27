module

public import Certificates.Kernel.LocalQT.He4090.L
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.H4090

open CFSG.KC.Enum CFSG.KC.LQT.PcW CFSG.QuasithinUnique.Vol2Native.L239.HePairs
open CFSG.QuasithinUnique.Ch1.SporLat.He

theorem b7a_t : Nat.beq (qtW 8330 14 16383 (TF 0) L7c b7a.w b7a.k) (TF 32) = true := by
  quickRfl

theorem b7a_i : Nat.beq (powS 8330 14 16383 (TF 0) (TF 32) (b7a.m - 1)) (TF 33) = true := by
  quickRfl

theorem b7a_ne : neB (TF 32) (TF 0) = true := by
  quickRfl

theorem b7a_3 : Nat.beq (powS 8330 14 16383 (TF 0) (TF 32) 3) (TF 0) = true := by
  quickRfl

theorem q7a_t : Nat.beq (qtW 8330 14 16383 (TF 0) L7c q7a.w q7a.k) (TF 34) = true := by
  quickRfl

theorem q7a_i : Nat.beq (powS 8330 14 16383 (TF 0) (TF 34) (q7a.m - 1)) (TF 35) = true := by
  quickRfl

theorem q7a_m : Nat.beq (powS 8330 14 16383 (TF 0) (TF 34) q7a.m) (TF 0) = true := by
  quickRfl

theorem q7a_l : labsK 8330 14 16383 (TF 34) heLabels7 = true := by
  quickRfl

theorem q7b_t : Nat.beq (qtW 8330 14 16383 (TF 0) L7c q7b.w q7b.k) (TF 36) = true := by
  quickRfl

theorem q7b_i : Nat.beq (powS 8330 14 16383 (TF 0) (TF 36) (q7b.m - 1)) (TF 37) = true := by
  quickRfl

theorem q7b_m : Nat.beq (powS 8330 14 16383 (TF 0) (TF 36) q7b.m) (TF 0) = true := by
  quickRfl

theorem q7b_l : labsK 8330 14 16383 (TF 36) heLabels7 = true := by
  quickRfl

theorem c1 : Nat.beq (commS 8330 14 16383 (TF 34) (TF 32) (TF 35) (TF 33)) (TF 39) = true := by
  quickRfl

theorem c2 : Nat.beq (commS 8330 14 16383 (TF 36) (TF 32) (TF 37) (TF 33)) (TF 40) = true := by
  quickRfl

theorem c11 : neB (pcS 8330 14 16383 (TF 39) (TF 39)) (TF 0) = true := by
  quickRfl

theorem b7p_t : Nat.beq (qtW 8330 14 16383 (TF 0) L7c b7p.w b7p.k) (TF 38) = true := by
  quickRfl

theorem b7p_ne : neB (TF 38) (TF 0) = true := by
  quickRfl

theorem b7p_7 : Nat.beq (powS 8330 14 16383 (TF 0) (TF 38) 7) (TF 0) = true := by
  quickRfl

theorem q7p_t : Nat.beq (qtW 8330 14 16383 (TF 0) L7c q7p.w q7p.k) (TF 36) = true := by
  quickRfl

theorem pq : neB (pcS 8330 14 16383 (TF 36) (TF 38)) (pcS 8330 14 16383 (TF 38) (TF 36)) = true := by
  quickRfl

end CFSG.KD.LQT.H4090

end
