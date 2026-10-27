module

public import Certificates.Kernel.M3BFib.FibData

public section

set_option maxRecDepth 100000

namespace CFSG.KC.M3BF

open CFSG.KD.M3BF
open Timmesfeld.M3B (sigW WT)

theorem m3bf_lk : LK = lk := by decide +kernel

theorem m3bf_t1 : adOfK LpM lk (sigW.getD 0 (WT.gen 0)) = t1 := by decide +kernel

theorem m3bf_t2 : adOfK LpM lk (sigW.getD 1 (WT.gen 0)) = t2 := by decide +kernel

theorem m3bf_t3 : adOfK LpM lk (sigW.getD 2 (WT.gen 0)) = t3 := by decide +kernel

end CFSG.KC.M3BF

end
