module

public import Certificates.Kernel.Sporadic.Fi24G2e.RData
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Sporadic.Fi24Fix.Split

#kc_repo #kc_ktree CFSG.KD.Fi24G2e RYS "Certificates/Kernel/Sporadic/Fi24G2e/data/rys.bin" 152491 4 1677401
  1924179683749408867

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e

@[expose] def yC (i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL LG (GWL i) CFSG.KD.BrFi24.ONE) (YY i)

@[expose] def zC (i : Nat) : Bool := Nat.beq (CFSG.KD.BrFi24.MUL (REP i) (YY i)) (ZZ i)

end CFSG.KD.Fi24G2e

namespace CFSG.KD.Fi24G2e.RY.Y

open CFSG.KD.Fi24G2e CFSG.KC.Fi24Fix

theorem yC_eq (i : Nat) :
    yC i = Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG (GWL i) CFSG.KD.BrFi24.ONE) (YY i) := rfl

theorem c0 : yC 0 = true := by quickRfl

theorem c1 : yC 1 = true := by quickRfl

theorem c2_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [6, 10] CFSG.KD.BrFi24.ONE) (RYS (nat_lit 0)) = true := by
  quickRfl

theorem c2_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [2, 4] (RYS (nat_lit 0))) (RYS (nat_lit 1)) = true := by
  quickRfl

theorem c2_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [10, 0] (RYS (nat_lit 1))) (YY 2) = true := by
  quickRfl

theorem c2 : yC 2 = true :=
  (yC_eq 2).trans <|
    beq_wordMul_of_eq (w' := [10, 0] ++ ([2, 4] ++ [6, 10])) rfl
    (beq_wordMul_append (beq_wordMul_append c2_2 c2_1) c2_0)

theorem c3 : yC 3 = true := by quickRfl

theorem c4 : yC 4 = true := by quickRfl

theorem c5_6 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [2, 3] CFSG.KD.BrFi24.ONE) (RYS (nat_lit 2)) = true := by
  quickRfl

theorem c5_5 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [3, 6] (RYS (nat_lit 2))) (RYS (nat_lit 3)) = true := by
  quickRfl

theorem c5_4 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [4, 7] (RYS (nat_lit 3))) (RYS (nat_lit 4)) = true := by
  quickRfl

theorem c5_3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [0, 2] (RYS (nat_lit 4))) (RYS (nat_lit 5)) = true := by
  quickRfl

theorem c5_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [3, 7] (RYS (nat_lit 5))) (RYS (nat_lit 6)) = true := by
  quickRfl

theorem c5_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [2, 6] (RYS (nat_lit 6))) (RYS (nat_lit 7)) = true := by
  quickRfl

theorem c5_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [3] (RYS (nat_lit 7))) (YY 5) = true := by
  quickRfl

theorem c5 : yC 5 = true :=
  (yC_eq 5).trans <|
    beq_wordMul_of_eq (w' := [3] ++ ([2, 6] ++ ([3, 7] ++ ([0, 2] ++ ([4, 7] ++ ([3, 6] ++ [2, 3])))))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c5_6 c5_5) c5_4) c5_3) c5_2) c5_1) c5_0)

theorem c6_3 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [1, 10] CFSG.KD.BrFi24.ONE) (RYS (nat_lit 8)) = true := by
  quickRfl

theorem c6_2 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [2, 4] (RYS (nat_lit 8))) (RYS (nat_lit 9)) = true := by
  quickRfl

theorem c6_1 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [1, 0] (RYS (nat_lit 9))) (RYS (nat_lit 10)) = true := by
  quickRfl

theorem c6_0 : Nat.beq (wordMul CFSG.KD.BrFi24.MUL LG [10] (RYS (nat_lit 10))) (YY 6) = true := by
  quickRfl

theorem c6 : yC 6 = true :=
  (yC_eq 6).trans <|
    beq_wordMul_of_eq (w' := [10] ++ ([1, 0] ++ ([2, 4] ++ [1, 10]))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append c6_3 c6_2) c6_1) c6_0)

theorem all : ∀ i < 7, yC i = true := by
  intro i hi
  match i, hi with
  | 0, _ => exact c0
  | 1, _ => exact c1
  | 2, _ => exact c2
  | 3, _ => exact c3
  | 4, _ => exact c4
  | 5, _ => exact c5
  | 6, _ => exact c6
  | _ + 7, _ => omega

end CFSG.KD.Fi24G2e.RY.Y


#kss_each CFSG.KD.Fi24G2e.RY.Z CFSG.KD.Fi24G2e.zC 7

end
