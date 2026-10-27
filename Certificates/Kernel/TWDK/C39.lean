module

public import Certificates.Kernel.TWDK.D39
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK39

open Certificates.TWDK

theorem frame : kFrameOK 3 9 F = true := by decide +kernel

theorem cover : kCover 9 S R = true := by decide +kernel

theorem lenS : S.length = 20 := by decide +kernel

theorem lenR : R.length = 4 := by decide +kernel

theorem neg_cover : (!kCover 9 S.tail R) = true := by decide +kernel

theorem neg_idx : (!kSingleAt 3 9 F (S.map fun e => (e.1, e.2.1, e.2.2.map (· + 1))) 0) = true := by
  decide +kernel

theorem neg_cut : (!kSingleAt 3 9 F (S.map fun e => (e.1, e.2.1, e.2.2.dropLast)) 0) = true := by
  decide +kernel

theorem neg_wit : (!kSingleAt 3 9 F
    (S.map fun e => (e.1, e.2.1.map (fun w => (w.1, w.2.1, w.2.2.1, 0 :: w.2.2.2)), e.2.2)) 0) =
      true := by
  decide +kernel

theorem neg_res : (!kResAt 3 9 F
    (R.map fun e => (e.1, e.2.1.map (fun w => (w.1, w.2.1, w.2.2.1, 0 :: w.2.2.2)),
      e.2.2.1.map (fun w => (w.1, w.2.1, w.2.2.1, 0 :: w.2.2.2)), e.2.2.2)) 0) = true := by
  decide +kernel

theorem neg_frame : (!kFrameOK 3 9 F.reverse) = true := by decide +kernel

end CFSG.KD.TWDK39

#kc_each CFSG.KD.TWDK39 s (Certificates.TWDK.kSingleAt 3 9 CFSG.KD.TWDK39.F CFSG.KD.TWDK39.S) 0 20

#kc_each CFSG.KD.TWDK39 r (Certificates.TWDK.kResAt 3 9 CFSG.KD.TWDK39.F CFSG.KD.TWDK39.R) 0 4

end
