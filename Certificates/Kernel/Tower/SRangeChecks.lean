module

public import Certificates.Data.Kernel.Tower.Search
public import Certificates.Kernel.Tower.SData
public import Certificates.Kernel.Tower.WrSData

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

theorem ch36409_u2 : allB 672 (fun r2 => Nat.blt (r2u2 (slSD 14) r2) 8192) = true := by
  decide +kernel

theorem ch36408_u2 : allB 24 (fun r2 => Nat.blt (r2u2 (wrSD 14) r2) 8192) = true := by
  decide +kernel

end Certificates.KernelTower
