module

public import Certificates.Data.FzBU
public import Certificates.Data.Kernel.FzUT.BMod
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.FzBMod

open Certificates.FzBU

@[expose] noncomputable def ch441796WL : List (List Nat) :=
  [[], [2, 0, 2, 0], [2, 1, 2, 1], [3, 1, 3, 1], [2], [0, 2, 0], [1, 2, 1], [2, 3, 1, 3, 1], [3],
    [3, 2, 0, 2, 0], [0, 3, 0], [1, 3, 1], [3, 2], [3, 0, 2, 0], [3, 1, 2, 1], [2, 1, 3, 1], [0],
    [2, 0, 2], [3, 0, 3], [0, 3, 1, 3, 1], [2, 0], [0, 2], [2, 3, 0, 3], [0, 1, 2, 1], [3, 0],
    [0, 1, 3, 1], [0, 3], [2, 0, 3, 2], [3, 2, 0], [3, 0, 2], [2, 0, 3], [0, 3, 2], [1],
    [1, 2, 0, 2, 0], [2, 1, 2], [3, 1, 3], [2, 1], [3, 1, 3, 2], [1, 2], [1, 0, 2, 0], [3, 1],
    [1, 0, 3, 0], [3, 2, 1, 2], [1, 3], [3, 2, 1], [1, 3, 2], [3, 1, 2], [2, 1, 3], [1, 0],
    [1, 2, 0, 2], [1, 3, 0, 3], [0, 3, 1, 3], [2, 1, 0], [0, 2, 1], [1, 2, 0], [1, 0, 2],
    [3, 1, 0], [1, 0, 3], [0, 3, 1], [1, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0], [1, 0, 3, 2],
    [1, 2, 0, 3]]

theorem ch441796_words : ((wordTab ()).toList == ch441796WL) = true := by quickRfl

@[expose] noncomputable def ch441796TabB (y : Array Nat) (T : Nat) : Bool :=
  allN 64 (fun x => Nat.beq (evalW y ((ch441796WL.toArray)[x]!)) (lk6 T x))

theorem ch441796_tab_q (c : Bool) : ch441796TabB ((repImgs c)[0]!) (tqT c) = true := by
  cases c <;> quickRfl

theorem ch441796_tab_s (c : Bool) : ch441796TabB ((repImgs c)[1]!) (tsT c) = true := by
  cases c <;> quickRfl

theorem ch441796_tab_y (c : Bool) : ch441796TabB ((repImgs c)[2]!) (tyT c) = true := by
  cases c <;> quickRfl

@[expose] noncomputable def ch441796ActB (c : Bool) : Bool :=
  allN 16 (fun w => allN 64 (fun u => Nat.beq (actL c w u)
    (itN (lk6 (tqT c)) (w % 4) (itN (lk6 (tsT c)) (w / 4 % 2) (itN (lk6 (tyT c)) (w / 8) u)))))

theorem ch441796_act (c : Bool) : ch441796ActB c = true := by
  cases c <;> quickRfl

theorem ch441796_umul : allN 64 (fun x => allN 64 (fun y => Nat.beq (uMulP x y) (uMul x y))) = true := by
  quickRfl

theorem ch441796_amul : allN 16 (fun w => allN 16 (fun v => Nat.beq (amulL w v) (amul w v))) = true := by
  quickRfl

end CFSG.KC.FzBMod
