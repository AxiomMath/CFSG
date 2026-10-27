module

public import Certificates.Kernel.Fi23P.KDefs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.KernelRfl

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KD.Fi23K CFSG.Sporadic.Th.Native
  CFSG.Monster.Existence.Fi23Sp8.Native

@[expose] def piL : List Nat := [4777, 6890, 30132, 8417, 16396, 3221, 4696, 23054, 16688, 3118]

@[expose] def tau (a x : Nat) : Nat := x ^^^ (if beta a x then a else 0)

set_option Elab.async false

theorem sig_ok : allN 255 (fun i => bAnd(Nat.blt (tb L 7 i) 31671, bAnd(Nat.beq (labP (tb L 7 i)) 0,
    bIf(Nat.blt i 254, Nat.blt (tb L 7 i) (tb L 7 (Nat.succ i)), true)))) = true := by quickRfl

theorem basis_ok : chooseBasis commK sigL = bLit := by
  unfold chooseBasis
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', ← Array.contains_toList, ← Array.all_toList]
  kernelRfl

theorem vec_ok : (List.range 255).all (fun i =>
    vecOfPt commK bLit (tb L 7 i) == tb L 5 (tb L 7 i)) = true := by
  unfold vecOfPt
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  quickRfl

theorem trans_ok : allN 10 (fun k => bIf(gOK k, allN 255 (fun i => strictB (tb L 7 i) fun q =>
    Nat.beq (tb L 5 (tb G k q)) (tau (tb L 5 (piL.getD k 0)) (tb L 5 q))), true)) = true := by
  quickRfl

theorem cnt0_ok : Nat.beq (sigL.countP fun p => commK p 4777) 127 = true := by quickRfl
theorem cnt1_ok : Nat.beq (sigL.countP fun p => commK p 16688) 45 = true := by quickRfl
theorem cnt2_ok : Nat.beq (sigL.countP fun p => commK p 0) 15 = true := by quickRfl

end CFSG.KD.Fi23P

end
