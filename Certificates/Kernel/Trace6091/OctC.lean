module

public import Certificates.Kernel.Trace6091.OddA0
public import Certificates.Kernel.Trace6091.OddC

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.AxisCount
  CFSG.Monster.Existence Finset

theorem octC_0 : octScanT PC (betaTabT PC) 0 69 = 0 := by decide +kernel

theorem octC_1 : octScanT PC (betaTabT PC) 69 69 = 0 := by decide +kernel

theorem octC_2 : octScanT PC (betaTabT PC) 138 69 = 0 := by decide +kernel

theorem octC_3 : octScanT PC (betaTabT PC) 207 69 = 0 := by decide +kernel

theorem octC_4 : octScanT PC (betaTabT PC) 276 69 = 0 := by decide +kernel

theorem octC_5 : octScanT PC (betaTabT PC) 345 69 = 0 := by decide +kernel

theorem octC_6 : octScanT PC (betaTabT PC) 414 69 = 0 := by decide +kernel

theorem octC_7 : octScanT PC (betaTabT PC) 483 69 = 0 := by decide +kernel

theorem octC_8 : octScanT PC (betaTabT PC) 552 69 = 0 := by decide +kernel

theorem octC_9 : octScanT PC (betaTabT PC) 621 69 = 0 := by decide +kernel

theorem octC_10 : octScanT PC (betaTabT PC) 690 69 = 0 := by decide +kernel

theorem octC_sum : ∑ o ∈ range 759, ∑ m ∈ range 64,
    xTerm permMonoC (Native.octCodeG (octT o) (evenT m))
      (Model.dualN (Native.spreadG (Model.wordN (octT o)) (evenT m))) = 0 := by
  refine (oct_block pe_PC [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] fun k hk => ?_).trans
    (by decide +kernel)
  interval_cases k
  exacts [octC_0, octC_1, octC_2, octC_3, octC_4, octC_5, octC_6, octC_7, octC_8, octC_9, octC_10]

theorem octBadC_1 : octScanT PBad (betaTabT PBad) 69 69 ≠ 0 := by decide +kernel

end Certificates.Kernel.Trace6091

end
