module

public import Certificates.Kernel.Q7Bits.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Q7Bits.Rec

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.KD.Q7Bits

#kc_each CFSG.KD.Q7Bits.rowOK 84 89
#kc_each CFSG.KD.Q7Bits.rowOK 90 91

open CFSG.Certificates.Kernel.Q7Bits CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
open CFSG.Certificates.Kernel.Q7Bits.Rec

#q7_rec CFSG.KD.Q7Bits.Q7R89 (rowN q7RepsData[nat_lit 89]!) (rt.getD (nat_lit 89) 0) (lv.getD (nat_lit 89) []) 120

theorem Q7R89.hb :
    (((rowN q7RepsData[nat_lit 89]!).x0 < 49 && (rowN q7RepsData[nat_lit 89]!).x1 < 49 && (rowN q7RepsData[nat_lit 89]!).x2 < 49 && (rowN q7RepsData[nat_lit 89]!).x3 < 49 &&
      (rowN q7RepsData[nat_lit 89]!).x4 < 49 && (rowN q7RepsData[nat_lit 89]!).x5 < 49 && (rowN q7RepsData[nat_lit 89]!).x6 < 49) &&
      (rowN q7RepsData[nat_lit 89]!).x3 == 1 && isFFN (rowN q7RepsData[nat_lit 89]!) && decide ((lv.getD (nat_lit 89) []).length ≤ 6) &&
      decide ((rt.getD (nat_lit 89) 0) < NL)) = true := by
  quickRfl

theorem Q7R89.hT :
    eqTabs (tabsOf (rowN q7RepsData[nat_lit 89]!)) Q7R89.T = true := by
  quickRfl

theorem Q7R89.hV :
    Nat.beq (vOf (rowN q7RepsData[nat_lit 89]!)) Q7R89.V = true := by
  quickRfl

theorem Q7R89.hr :
    Q7R89.V.testBit ((rt.getD (nat_lit 89) 0) + 64) = true := by
  quickRfl

theorem Q7R89.h0 :
    Nat.beq (2 ^ ((rt.getD (nat_lit 89) 0) + 64)) Q7R89.S0 = true := by
  quickRfl

theorem Q7R89.hl :
    Nat.beq (lv.getD (nat_lit 89) []).length 3 = true := by
  quickRfl

theorem Q7R89.c0_1 :
    optB (stepL MM Q7R89.T Q7R89.V Q7R89.S0 (rowN q7RepsData[nat_lit 89]!)
      (((lv.getD (nat_lit 89) []).getD 0 []).drop 0) Q7R89.S0) Q7R89.A0_1 = true := by
  quickRfl

theorem Q7R89.c1_1 :
    optB (stepL MM Q7R89.T Q7R89.V Q7R89.A0_1 (rowN q7RepsData[nat_lit 89]!)
      ((((lv.getD (nat_lit 89) []).getD 1 []).drop 0).take 120) Q7R89.A0_1) Q7R89.A1_1 = true := by
  quickRfl

theorem Q7R89.c1_2 :
    optB (stepL MM Q7R89.T Q7R89.V Q7R89.A0_1 (rowN q7RepsData[nat_lit 89]!)
      ((((lv.getD (nat_lit 89) []).getD 1 []).drop 120).take 120) Q7R89.A1_1) Q7R89.A1_2 = true := by
  quickRfl

theorem Q7R89.c1_3 :
    optB (stepL MM Q7R89.T Q7R89.V Q7R89.A0_1 (rowN q7RepsData[nat_lit 89]!)
      (((lv.getD (nat_lit 89) []).getD 1 []).drop 240) Q7R89.A1_2) Q7R89.A1_3 = true := by
  quickRfl

theorem Q7R89.c2_1 :
    optB (stepL MM Q7R89.T Q7R89.V Q7R89.A1_3 (rowN q7RepsData[nat_lit 89]!)
      ((((lv.getD (nat_lit 89) []).getD 2 []).drop 0).take 120) Q7R89.A1_3) Q7R89.A2_1 = true := by
  quickRfl

theorem Q7R89.c2_2 :
    optB (stepL MM Q7R89.T Q7R89.V Q7R89.A1_3 (rowN q7RepsData[nat_lit 89]!)
      (((lv.getD (nat_lit 89) []).getD 2 []).drop 120) Q7R89.A2_1) Q7R89.A2_2 = true := by
  quickRfl

theorem Q7R89.hf :
    (Nat.land Q7R89.V (Nat.xor Q7R89.A2_2 MM) >>> 64 == 0) = true := by
  quickRfl

theorem rowOK89 : rowOK (nat_lit 89) = true := by
  have l0 : stepL MM Q7R89.T Q7R89.V Q7R89.S0 (rowN q7RepsData[nat_lit 89]!)
      ((lv.getD (nat_lit 89) []).getD 0 []) Q7R89.S0 = some Q7R89.A0_1 :=
    stepL_drop0 (eq_of_optB Q7R89.c0_1)
  have l1 : stepL MM Q7R89.T Q7R89.V Q7R89.A0_1 (rowN q7RepsData[nat_lit 89]!)
      ((lv.getD (nat_lit 89) []).getD 1 []) Q7R89.A0_1 = some Q7R89.A1_3 :=
    stepL_drop0 ((stepL_chunk (d := 0) (k := 120) (d' := 120) rfl (eq_of_optB Q7R89.c1_1)
        ((stepL_chunk (d := 120) (k := 120) (d' := 240) rfl (eq_of_optB Q7R89.c1_2)
        (eq_of_optB Q7R89.c1_3)))))
  have l2 : stepL MM Q7R89.T Q7R89.V Q7R89.A1_3 (rowN q7RepsData[nat_lit 89]!)
      ((lv.getD (nat_lit 89) []).getD 2 []) Q7R89.A1_3 = some Q7R89.A2_2 :=
    stepL_drop0 ((stepL_chunk (d := 0) (k := 120) (d' := 120) rfl (eq_of_optB Q7R89.c2_1)
        (eq_of_optB Q7R89.c2_2)))
  exact rowCheck_of Q7R89.hb (rowCore_of Q7R89.hT Q7R89.hV Q7R89.hr Q7R89.h0
    (runLv3_of Q7R89.hl l0 l1 l2) Q7R89.hf)

end CFSG.KD.Q7Bits
