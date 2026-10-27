module

public import Certificates.Data.Kernel.Tower.Cls14
public import Certificates.Kernel.Tower.E14Checks
public import Certificates.Kernel.Tower.E14XData

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def e14Pc (D : Nat → Nat) (a g nl : Nat) : Bool :=
  pcB 16384 (slEm a g) (D 0) (D 1) (D 2) (D 3) nl 128 (l16 (D 5) 0)

@[expose] noncomputable def e14Chi (D : Nat → Nat) (j a g : Nat) : Bool :=
  chiB 16384 (slEm a g) (D 5) (slX j) 128 (l16 (D 5) 0)

theorem ch36409_e0_pc : e14Pc slE0 0 132 100 = true := by decide +kernel
theorem ch36409_e1_pc : e14Pc slE1 2 132 94 = true := by decide +kernel
theorem ch36409_e2_pc : e14Pc slE2 9 0 100 = true := by decide +kernel
theorem ch36409_e3_pc : e14Pc slE3 11 0 94 = true := by decide +kernel

theorem ch36409_e0_chi : e14Chi slE0 0 0 132 = true := by decide +kernel
theorem ch36409_e1_chi : e14Chi slE1 1 2 132 = true := by decide +kernel
theorem ch36409_e2_chi : e14Chi slE2 2 9 0 = true := by decide +kernel
theorem ch36409_e3_chi : e14Chi slE3 3 11 0 = true := by decide +kernel

end Certificates.KernelTower
