module

public import Certificates.Kernel.Q7Bits.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Q7Bits.Rec

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.KD.Q7Bits

#kc_each CFSG.KD.Q7Bits.rowOK 0 2
#kc_each CFSG.KD.Q7Bits.rowOK 3 7

open CFSG.Certificates.Kernel.Q7Bits CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
open CFSG.Certificates.Kernel.Q7Bits.Rec

#q7_rec CFSG.KD.Q7Bits.Q7R2 (rowN q7RepsData[nat_lit 2]!) (rt.getD (nat_lit 2) 0) (lv.getD (nat_lit 2) []) 120

theorem Q7R2.hb :
    (((rowN q7RepsData[nat_lit 2]!).x0 < 49 && (rowN q7RepsData[nat_lit 2]!).x1 < 49 && (rowN q7RepsData[nat_lit 2]!).x2 < 49 && (rowN q7RepsData[nat_lit 2]!).x3 < 49 &&
      (rowN q7RepsData[nat_lit 2]!).x4 < 49 && (rowN q7RepsData[nat_lit 2]!).x5 < 49 && (rowN q7RepsData[nat_lit 2]!).x6 < 49) &&
      (rowN q7RepsData[nat_lit 2]!).x3 == 1 && isFFN (rowN q7RepsData[nat_lit 2]!) && decide ((lv.getD (nat_lit 2) []).length ≤ 6) &&
      decide ((rt.getD (nat_lit 2) 0) < NL)) = true := by
  quickRfl

theorem Q7R2.hT :
    eqTabs (tabsOf (rowN q7RepsData[nat_lit 2]!)) Q7R2.T = true := by
  quickRfl

theorem Q7R2.hV :
    Nat.beq (vOf (rowN q7RepsData[nat_lit 2]!)) Q7R2.V = true := by
  quickRfl

theorem Q7R2.hr :
    Q7R2.V.testBit ((rt.getD (nat_lit 2) 0) + 64) = true := by
  quickRfl

theorem Q7R2.h0 :
    Nat.beq (2 ^ ((rt.getD (nat_lit 2) 0) + 64)) Q7R2.S0 = true := by
  quickRfl

theorem Q7R2.hl :
    Nat.beq (lv.getD (nat_lit 2) []).length 3 = true := by
  quickRfl

theorem Q7R2.c0_1 :
    optB (stepL MM Q7R2.T Q7R2.V Q7R2.S0 (rowN q7RepsData[nat_lit 2]!)
      (((lv.getD (nat_lit 2) []).getD 0 []).drop 0) Q7R2.S0) Q7R2.A0_1 = true := by
  quickRfl

theorem Q7R2.c1_1 :
    optB (stepL MM Q7R2.T Q7R2.V Q7R2.A0_1 (rowN q7RepsData[nat_lit 2]!)
      ((((lv.getD (nat_lit 2) []).getD 1 []).drop 0).take 120) Q7R2.A0_1) Q7R2.A1_1 = true := by
  quickRfl

theorem Q7R2.c1_2 :
    optB (stepL MM Q7R2.T Q7R2.V Q7R2.A0_1 (rowN q7RepsData[nat_lit 2]!)
      ((((lv.getD (nat_lit 2) []).getD 1 []).drop 120).take 120) Q7R2.A1_1) Q7R2.A1_2 = true := by
  quickRfl

theorem Q7R2.c1_3 :
    optB (stepL MM Q7R2.T Q7R2.V Q7R2.A0_1 (rowN q7RepsData[nat_lit 2]!)
      (((lv.getD (nat_lit 2) []).getD 1 []).drop 240) Q7R2.A1_2) Q7R2.A1_3 = true := by
  quickRfl

theorem Q7R2.c2_1 :
    optB (stepL MM Q7R2.T Q7R2.V Q7R2.A1_3 (rowN q7RepsData[nat_lit 2]!)
      ((((lv.getD (nat_lit 2) []).getD 2 []).drop 0).take 120) Q7R2.A1_3) Q7R2.A2_1 = true := by
  quickRfl

theorem Q7R2.c2_2 :
    optB (stepL MM Q7R2.T Q7R2.V Q7R2.A1_3 (rowN q7RepsData[nat_lit 2]!)
      (((lv.getD (nat_lit 2) []).getD 2 []).drop 120) Q7R2.A2_1) Q7R2.A2_2 = true := by
  quickRfl

theorem Q7R2.hf :
    (Nat.land Q7R2.V (Nat.xor Q7R2.A2_2 MM) >>> 64 == 0) = true := by
  quickRfl

theorem rowOK2 : rowOK (nat_lit 2) = true := by
  have l0 : stepL MM Q7R2.T Q7R2.V Q7R2.S0 (rowN q7RepsData[nat_lit 2]!)
      ((lv.getD (nat_lit 2) []).getD 0 []) Q7R2.S0 = some Q7R2.A0_1 :=
    stepL_drop0 (eq_of_optB Q7R2.c0_1)
  have l1 : stepL MM Q7R2.T Q7R2.V Q7R2.A0_1 (rowN q7RepsData[nat_lit 2]!)
      ((lv.getD (nat_lit 2) []).getD 1 []) Q7R2.A0_1 = some Q7R2.A1_3 :=
    stepL_drop0 ((stepL_chunk (d := 0) (k := 120) (d' := 120) rfl (eq_of_optB Q7R2.c1_1)
        ((stepL_chunk (d := 120) (k := 120) (d' := 240) rfl (eq_of_optB Q7R2.c1_2)
        (eq_of_optB Q7R2.c1_3)))))
  have l2 : stepL MM Q7R2.T Q7R2.V Q7R2.A1_3 (rowN q7RepsData[nat_lit 2]!)
      ((lv.getD (nat_lit 2) []).getD 2 []) Q7R2.A1_3 = some Q7R2.A2_2 :=
    stepL_drop0 ((stepL_chunk (d := 0) (k := 120) (d' := 120) rfl (eq_of_optB Q7R2.c2_1)
        (eq_of_optB Q7R2.c2_2)))
  exact rowCheck_of Q7R2.hb (rowCore_of Q7R2.hT Q7R2.hV Q7R2.hr Q7R2.h0
    (runLv3_of Q7R2.hl l0 l1 l2) Q7R2.hf)

end CFSG.KD.Q7Bits
