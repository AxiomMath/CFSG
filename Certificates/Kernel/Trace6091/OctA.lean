module

public import Certificates.Kernel.Trace6091.OddA0
public import CFSG.Certificates.Kernel.Trace6091.ScanRest

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.AxisCount
  CFSG.Monster.Existence Finset

theorem octA_0 : octScanT PA (betaTabT PA) 0 69 = 36 := by decide +kernel

theorem octA_1 : octScanT PA (betaTabT PA) 69 69 = 20 := by decide +kernel

theorem octA_2 : octScanT PA (betaTabT PA) 138 69 = 4 := by decide +kernel

theorem octA_3 : octScanT PA (betaTabT PA) 207 69 = 0 := by decide +kernel

theorem octA_4 : octScanT PA (betaTabT PA) 276 69 = 24 := by decide +kernel

theorem octA_5 : octScanT PA (betaTabT PA) 345 69 = 8 := by decide +kernel

theorem octA_6 : octScanT PA (betaTabT PA) 414 69 = 24 := by decide +kernel

theorem octA_7 : octScanT PA (betaTabT PA) 483 69 = 8 := by decide +kernel

theorem octA_8 : octScanT PA (betaTabT PA) 552 69 = 0 := by decide +kernel

theorem octA_9 : octScanT PA (betaTabT PA) 621 69 = 8 := by decide +kernel

theorem octA_10 : octScanT PA (betaTabT PA) 690 69 = 24 := by decide +kernel

theorem octA_sum : ∑ o ∈ range 759, ∑ m ∈ range 64,
    xTerm permMonoA (Native.octCodeG (octT o) (evenT m))
      (Model.dualN (Native.spreadG (Model.wordN (octT o)) (evenT m))) = 156 := by
  refine (oct_block pe_PA [36, 20, 4, 0, 24, 8, 24, 8, 0, 8, 24] fun k hk => ?_).trans
    (by decide +kernel)
  interval_cases k
  exacts [octA_0, octA_1, octA_2, octA_3, octA_4, octA_5, octA_6, octA_7, octA_8, octA_9, octA_10]

theorem octBad_1 : octScanT PBad (betaTabT PBad) 69 69 ≠ 20 := by decide +kernel

end Certificates.Kernel.Trace6091

end
