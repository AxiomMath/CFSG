module

public import Certificates.Kernel.TWDK.D77
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK77

open Certificates.TWDK

theorem frame : kFrameOK 7 7 F = true := by decide +kernel

theorem cover : kCover 7 S R = true := by decide +kernel

theorem lenS : S.length = 16 := by decide +kernel

theorem lenR : R.length = 4 := by decide +kernel

theorem neg_cover : (!kCover 7 S.tail R) = true := by decide +kernel

end CFSG.KD.TWDK77

#kc_each CFSG.KD.TWDK77 s (Certificates.TWDK.kSingleAt 7 7 CFSG.KD.TWDK77.F CFSG.KD.TWDK77.S) 0 8

end
