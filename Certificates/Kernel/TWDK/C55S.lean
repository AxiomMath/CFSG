module

public import Certificates.Kernel.TWDK.D55
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK55

open Certificates.TWDK

theorem frame : kFrameOK 5 5 F = true := by decide +kernel

theorem cover : kCover 5 S R = true := by decide +kernel

theorem lenS : S.length = 12 := by decide +kernel

theorem lenR : R.length = 4 := by decide +kernel

end CFSG.KD.TWDK55

#kc_each CFSG.KD.TWDK55 s (Certificates.TWDK.kSingleAt 5 5 CFSG.KD.TWDK55.F CFSG.KD.TWDK55.S) 0 12

end
