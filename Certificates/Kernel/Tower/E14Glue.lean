module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerCode
public import Certificates.Data.Kernel.Tower.W
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace Certificates.KernelTower

open Certificates.KernelTower CFSG.OddStandard.AltStdSmall4.Tower

theorem allB_two {p : Nat → Bool} (h0 : p 0 = true) (h1 : p 1 = true) : allB 2 p = true := by
  change (p 1 && (p 0 && true)) = true
  rw [h0, h1]
  rfl

end Certificates.KernelTower
