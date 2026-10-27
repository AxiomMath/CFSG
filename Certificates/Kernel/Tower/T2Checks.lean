module

public import Certificates.Data.Kernel.Tower.T2Sq
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Kernel.Tower.SData
public import Certificates.Kernel.Tower.T2Data

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def slT2At (a : Nat) : Bool :=
  t2At (wm slSM slAC) wGS (slSD 4) slT2.b0 slT2.b1 (slA (Nat.add a 2)) a

theorem ch36409_t2 : allB 32 slT2At = true := by decide +kernel

end Certificates.KernelTower
