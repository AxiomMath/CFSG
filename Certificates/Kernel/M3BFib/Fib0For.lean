module

public import Certificates.Kernel.M3BFib.Fib0Data

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF

theorem m3bf_for0_0 : (rowsK0 kM dT tb o0_0 (mk.getD 0 0) == some (mk.getD 1 0)) = true := by
  decide +kernel

theorem m3bf_for0_1 : (rowsK0 kM dT tb o0_1 (mk.getD 1 0) == some (mk.getD 2 0)) = true := by
  decide +kernel

theorem m3bf_for0_2 : (rowsK0 kM dT tb o0_2 (mk.getD 2 0) == some (mk.getD 3 0)) = true := by
  decide +kernel

theorem m3bf_for0_3 : (rowsK0 kM dT tb o0_3 (mk.getD 3 0) == some (mk.getD 4 0)) = true := by
  decide +kernel

theorem m3bf_for0_4 : (rowsK0 kM dT tb o0_4 (mk.getD 4 0) == some (mk.getD 5 0)) = true := by
  decide +kernel

theorem m3bf_for0_5 : (rowsK0 kM dT tb o0_5 (mk.getD 5 0) == some (mk.getD 6 0)) = true := by
  decide +kernel

theorem m3bf_for0_6 : (rowsK0 kM dT tb o0_6 (mk.getD 6 0) == some (mk.getD 7 0)) = true := by
  decide +kernel

theorem m3bf_for0_7 : (rowsK0 kM dT tb o0_7 (mk.getD 7 0) == some (mk.getD 8 0)) = true := by
  decide +kernel

end CFSG.KC.M3BF

end
