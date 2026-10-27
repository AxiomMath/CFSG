module

public import Certificates.Data.Kernel.Tower.Word
public import Certificates.Kernel.Tower.L3Checks
public import Certificates.Kernel.Tower.L3WData
import CFSG.Certificates.Kernel.Common.Each

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def l3G (f : Nat) : Nat := wrL3W (Nat.mul 18 f)

@[expose] noncomputable def l3Wd (f : Nat) : Nat := wrL3W (Nat.add (Nat.mul 18 f) 1)

@[expose] noncomputable def l3Im (f j : Nat) : Nat := wrL3W (Nat.add (Nat.mul 18 f) (Nat.add 2 j))

@[expose] noncomputable def l3g2 (f j : Nat) : Nat := l16 (l3G f) (Nat.add 4 j)

@[expose] noncomputable def ch36408_l3t (f : Nat) : Bool :=
  Nat.beq (l16 (wrA (Nat.add 2 (l16 (l3P f) 0))) 1) 1 &&
    allB 16 fun j => tgtOK (l3M f) wGS (Nat.shiftRight (l3P f) 48) (l16 (l3P f) 2) (l3G f) (l3Im f j)
      (l3Wd f) (l3X f j) (l3H f j) (l3g2 f j)

#kc_each ch36408_l3t 0 28

theorem ch36408_l3c : allB 8192 (fun c => Nat.beq (wm wrSM wrAC 1 c) (wm wrSM wrAC c 1)) = true := by
  decide +kernel

theorem ch36408_l3t_neg :
    (!tgtOK (l3M 0) wGS (Nat.shiftRight (l3P 0) 48) (l16 (l3P 0) 2) (l3G 0)
      (Nat.xor (l3Im 0 1) 2) (l3Wd 0) (l3X 0 1) (l3H 0 1) (l3g2 0 1)) = true := by
  decide +kernel

end Certificates.KernelTower
