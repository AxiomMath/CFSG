module

public import CFSG.Certificates.Kernel.SortTreeSlice
public import Certificates.Kernel.MonsterB.Mono3016Data
public import CFSG.Monster.B.TwoA.Census.MonoCertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Mono3016

open CFSG.KC.SortTree CFSG.KLie.CT CFSG.Monster.B.TwoA.Census

set_option maxRecDepth 100000

@[expose] noncomputable def permR (P n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => nIf(bit n j, Nat.add ih (pw2 (fget P j 5)), ih)) m

@[expose] noncomputable def canIK (n : Nat) : Nat :=
  (fun x => nIf(Nat.ble n x, n, x)) (Nat.xor n 16777215)

@[expose] noncomputable def actJR (j k n : Nat) : Nat :=
  nIf(Nat.blt k 12, canIK (Nat.xor n (fget XJ (Nat.add (Nat.mul 12 j) k) 24)),
    canIK (permR (fget PJ (Nat.add (Nat.mul 5 j) (Nat.sub k 12)) 120) n 24))

@[expose] noncomputable def recI (o t : Nat) : Nat := recT M 6 48 (Nat.add o t)

@[expose] noncomputable def edgeI (o t k : Nat) : Nat := fget (recT ME 6 188 (Nat.add o t)) k 11

@[expose] noncomputable def validRec (j o n : Nat) : Bool :=
  (List.range n).all fun t =>
    (fun v w => decide (v < 2 ^ 23) && decide (w < 4096) && combI w == v && eligB j v)
      (valF 24 (recI o t)) (recT WT 6 12 (Nat.add o t))

@[expose] noncomputable def disjI (o n o' n' : Nat) : Bool :=
  allN n fun a => (fun v => allN n' fun b => notB (Nat.beq v (valF 24 (recI o' b))))
    (valF 24 (recI o a))

@[expose] noncomputable def par24 (y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.xor ih (Nat.land (Nat.shiftRight y i) 1)) 24

@[expose] noncomputable def decD (x : Nat) : Nat :=
  orN 12 fun k => Nat.shiftLeft (par24 (Nat.land x (fget DD k 24))) k

theorem t0 : treeOK (actJR 0) 14 (fun _ => true) 0 (recI 0) 1 24 5 11 64 1 = true := by quickRfl
theorem t1 : treeOK (actJR 0) 14 (fun _ => true) 255 (recI 1) 759 24 5 11 64 12 = true := by
  quickRfl
theorem t2 : treeOK (actJR 0) 14 (fun _ => true) 212822 (recI 760) 1288 24 5 11 64 21 = true := by
  quickRfl
theorem t3 : treeOK (actJR 1) 17 (fun _ => true) 0 (recI 2048) 16 24 5 11 64 1 = true := by
  quickRfl
theorem t4 : treeOK (actJR 1) 17 (fun _ => true) 197482 (recI 2064) 112 24 5 11 64 2 = true := by
  quickRfl
theorem t5 : treeOK (actJR 2) 17 (fun _ => true) 0 (recI 2176) 32 24 5 11 64 1 = true := by
  quickRfl
theorem t6 : treeOK (actJR 2) 17 (fun _ => true) 3346236 (recI 2208) 32 24 5 11 64 1 = true := by
  quickRfl

theorem e0 : closeOK (actJR 0) 14 (recI 0) (edgeI 0) 1 24 64 1 = true := by quickRfl
theorem e1 : closeOK (actJR 0) 14 (recI 1) (edgeI 1) 759 24 64 12 = true := by quickRfl
theorem e2 : closeOK (actJR 0) 14 (recI 760) (edgeI 760) 1288 24 64 21 = true := by quickRfl
theorem e3 : closeOK (actJR 1) 17 (recI 2048) (edgeI 2048) 16 24 64 1 = true := by quickRfl
theorem e4 : closeOK (actJR 1) 17 (recI 2064) (edgeI 2064) 112 24 64 2 = true := by quickRfl
theorem e5 : closeOK (actJR 2) 17 (recI 2176) (edgeI 2176) 32 24 64 1 = true := by quickRfl
theorem e6 : closeOK (actJR 2) 17 (recI 2208) (edgeI 2208) 32 24 64 1 = true := by quickRfl

theorem v0 : validRec 0 0 1 = true := by decide +kernel
theorem v1 : validRec 0 1 759 = true := by decide +kernel
theorem v2 : validRec 0 760 1288 = true := by decide +kernel
theorem v3 : validRec 1 2048 16 = true := by decide +kernel
theorem v4 : validRec 1 2064 112 = true := by decide +kernel
theorem v5 : validRec 2 2176 32 = true := by decide +kernel
theorem v6 : validRec 2 2208 32 = true := by decide +kernel

theorem d01 : disjI 0 1 1 759 = true := by quickRfl
theorem d02 : disjI 0 1 760 1288 = true := by quickRfl
theorem d12 : disjI 1 759 760 1288 = true := by quickRfl
theorem d34 : disjI 2048 16 2064 112 = true := by quickRfl
theorem d56 : disjI 2176 32 2208 32 = true := by quickRfl

theorem kDec : (List.range 4096).all (fun m => decD (combI m) == m) = true := by decide +kernel

end CertificateChecks.Mono3016

end
