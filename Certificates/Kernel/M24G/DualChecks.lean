module

public import Certificates.Data.Kernel.M24G.Dual
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.DualData

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.DualC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem lu_ok : allIdx (fun i x => Native.trioIn x SL.toArray[0]! == DualD.LU.contains i) TL 0 =
    true := by decide +kernel

theorem lu_asc : ascL DualD.LU = true := by decide +kernel

theorem lu_lt : ∀ x ∈ DualD.LU, x < Native.nTrio := by decide +kernel

set_option maxHeartbeats 0 in
theorem tu_ok : DualD.LU.all (fun a => TL.toArray[a]! == tabLU DualD.LU DualD.TU a) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem dual_ok : dualCk DualD.LU (tabLU DualD.LU DualD.TU) (Native.octsS SL.toArray[0]!) = true := by
  decide +kernel

end CFSG.KC.M24G.DualC
