module

public import Certificates.Data.Kernel.M24G.Trio12
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.Trio12Data

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.T12C

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem tB_eq : Native.tTabs.map (fun t => imgTab t.toList) = T12D.tB := by decide +kernel

theorem lB_eq : Native.lTabs.map (fun t => imgTab t.toList) = T12D.lB := by decide +kernel

theorem b7_ok : allIdx (fun i x => Native.trioIn Native.baseTrio x == T12D.B7.contains i) SL 0 =
    true := by
  decide +kernel

theorem b7_asc : ascL T12D.B7 = true := by decide +kernel

theorem b7_lt : ∀ x ∈ T12D.B7, x < Native.nSext := by decide +kernel

theorem genFix_ok : genFixF T12D.tB SL T12D.B7 = true := by decide +kernel

theorem base_ok : [Native.baseSext, Native.sextU2, Native.sextU3].all
    (fun U => Native.trioIn Native.baseTrio U && SL.contains U) = true := by
  decide +kernel

theorem idx0_ok : idxK (posTree Native.key3 TL) 3795 0 = 3795 := by decide +kernel

end CFSG.KC.M24G.T12C
