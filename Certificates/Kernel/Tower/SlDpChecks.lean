module

public import Certificates.Data.Kernel.Tower.L1
public import Certificates.Kernel.Tower.T2Data
public import Certificates.Data.Kernel.Tower.Tree

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] def slDeep (a k : Nat) : Bool :=
  Nat.beq k 0 && (Nat.beq a 0 || Nat.beq a 2 || Nat.beq a 9 || Nat.beq a 11)

@[expose] noncomputable def slGL (a k : Nat) : Nat := l16 slT2.b0 (Nat.add (Nat.mul 2 a) k)

@[expose] noncomputable def slDP (DP a : Nat) : Bool :=
  allB 2 fun k => slDeep a k || !Nat.beq (bit DP (Nat.add (Nat.mul 2 a) k)) 1

theorem ch36409_dp : allB 32 (slDP slT2.b1) = true := by decide +kernel

theorem slGL_0 : slGL 0 0 = 132 := by decide +kernel
theorem slGL_2 : slGL 2 0 = 132 := by decide +kernel
theorem slGL_9 : slGL 9 0 = 0 := by decide +kernel
theorem slGL_11 : slGL 11 0 = 0 := by decide +kernel

end Certificates.KernelTower
