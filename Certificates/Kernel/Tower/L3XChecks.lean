module

public import Certificates.Data.Kernel.Tower.Chi
public import Certificates.Kernel.Tower.L3Checks
public import Certificates.Kernel.Tower.L3XData
import CFSG.Certificates.Kernel.Common.Each

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

theorem ch36408_par : parOK = true := by decide +kernel

@[expose] noncomputable def ch36408_chw (i : Nat) : Bool := chiWOK wrSM wrAC (wrChi i)

#kc_each ch36408_chw 0 16

@[expose] noncomputable def ch36408_l3x (f : Nat) : Bool :=
  allB 16 fun j => chiXOK wrChi (wrA (Nat.add 2 (l16 (l3P f) 0))) (l16 (l3P f) 1) wGS (l3X f j)

#kc_each ch36408_l3x 0 28

theorem ch36408_l3g : allB 28 (fun f => Nat.blt (l16 (l3P f) 1) 8192) = true := by
  decide +kernel

theorem ch36408_l3z : allB 16384 (fun k =>
    Nat.beq (Nat.add (Nat.mul 2 (wm wrSM wrAC 1 (Nat.shiftRight k 1))) (Nat.land k 1))
      (Nat.xor k 2)) = true := by
  decide +kernel

theorem ch36408_chw_neg : (!chiWOK wrSM wrAC (Nat.xor (wrChi 1) 1)) = true := by decide +kernel

theorem ch36408_l3x_neg :
    (!chiXOK wrChi (wrA (Nat.add 2 (l16 (l3P 0) 0))) (l16 (l3P 0) 1) wGS
      (Nat.xor (l3X 0 1) (Nat.shiftLeft 1 3))) = true := by
  decide +kernel

end Certificates.KernelTower
