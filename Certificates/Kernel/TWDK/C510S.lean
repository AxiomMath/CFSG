module

public import Certificates.Kernel.TWDK.D510
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK510

open Certificates.TWDK

theorem frame : kFrameOK 5 10 F = true := by decide +kernel

theorem cover : kCover 10 S R = true := by decide +kernel

theorem lenS : S.length = 20 := by decide +kernel

theorem lenR : R.length = 4 := by decide +kernel

theorem neg_cover : (!kCover 10 S.tail R) = true := by decide +kernel

end CFSG.KD.TWDK510

#kc_each CFSG.KD.TWDK510 s (Certificates.TWDK.kSingleAt 5 10 CFSG.KD.TWDK510.F CFSG.KD.TWDK510.S)
  0 20

end
