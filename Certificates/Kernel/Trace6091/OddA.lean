module

public import Certificates.Kernel.Trace6091.OddA0
public import CFSG.Certificates.Kernel.Trace6091.ScanRest

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.Existence Finset

theorem oddA_1 : oddScanT PA (betaTabT PA) 256 256 = 24 := by decide +kernel

theorem oddA_2 : oddScanT PA (betaTabT PA) 512 256 = 24 := by decide +kernel

theorem oddA_3 : oddScanT PA (betaTabT PA) 768 256 = 24 := by decide +kernel

theorem oddA_4 : oddScanT PA (betaTabT PA) 1024 256 = 24 := by decide +kernel

theorem oddA_5 : oddScanT PA (betaTabT PA) 1280 256 = 24 := by decide +kernel

theorem oddA_6 : oddScanT PA (betaTabT PA) 1536 256 = 24 := by decide +kernel

theorem oddA_7 : oddScanT PA (betaTabT PA) 1792 256 = 24 := by decide +kernel

theorem oddA_sum : ∑ t ∈ range 2048, ∑ i ∈ range 24,
    xTerm permMonoA (Model.oddCode (2 * t) i) (Model.dualN (2 ^ i)) = 192 := by
  refine (odd_block pe_PA [24, 24, 24, 24, 24, 24, 24, 24] fun k hk => ?_).trans (by decide +kernel)
  interval_cases k
  exacts [oddA_0, oddA_1, oddA_2, oddA_3, oddA_4, oddA_5, oddA_6, oddA_7]

end Certificates.Kernel.Trace6091

end
