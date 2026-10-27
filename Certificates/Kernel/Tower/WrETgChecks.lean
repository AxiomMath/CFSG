module

public import Certificates.Kernel.Tower.WrEChecks

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def ch36408_etg (e : Nat) : Bool :=
  allB (Nat.mul 16 (wrEP e 10)) fun q => Nat.blt (l16 (wrTG (wrEP e 9) q) 3) 16384

theorem ch36408_etg_all : allB 12 ch36408_etg = true := by decide +kernel

end Certificates.KernelTower
