module

public import Certificates.Kernel.TWDK.D36
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK36

open Certificates.TWDK Certificates.TWDK36

theorem frame : kFrameOK 3 6 F = true := by decide +kernel

theorem cover : kCover36 6 S T = true := by decide +kernel

theorem lenS : S.length = 14 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel

theorem neg_cover : (!kCover36 6 S.tail T) = true := by decide +kernel

theorem neg_cover2 : (!kCover36 6 S T.tail) = true := by decide +kernel

theorem neg_idx : (!kOneAt 3 6 F O (S.map fun e => (e.1, e.2.1, e.2.2.map fun c => (c.1, c.2 + 1)))
    1) = true := by
  decide +kernel

theorem neg_idx2 : (!kTwoAt 3 6 F O (T.map fun e => (e.1, e.2.1,
    e.2.2.1.map (fun o => (o.1 + 1, o.2)), e.2.2.2)) 0) = true := by
  decide +kernel

theorem neg_wit : (!kOneAt 3 6 F O
    (S.map fun e => (e.1, e.2.1.map (fun w => (w.1, w.2.1, w.2.2.1, 0 :: w.2.2.2)), e.2.2)) 1) =
      true := by
  decide +kernel

theorem neg_wit2 : (!kTwoAt 3 6 F O
    (T.map fun e => (e.1, e.2.1.map (fun w => (w.1, w.2.1, w.2.2.1, 0 :: w.2.2.2)), e.2.2)) 0) =
      true := by
  decide +kernel

theorem neg_kind : (!kOneAt 3 6 F O
    (S.map fun e => (e.1, e.2.1, e.2.2.map fun c => (true, c.2))) 1) = true := by
  decide +kernel

theorem neg_out : (!kOneAt 3 6 F (O.map fun o => (o.1, o.2.1, (0, 0) :: o.2.2.tail)) S 0) =
    true := by
  decide +kernel

theorem neg_frame : (!kFrameOK 3 6 F.reverse) = true := by decide +kernel

end CFSG.KD.TWDK36

#kc_each CFSG.KD.TWDK36 s (Certificates.TWDK36.kOneAt 3 6 CFSG.KD.TWDK36.F CFSG.KD.TWDK36.O
  CFSG.KD.TWDK36.S) 0 14

#kc_each CFSG.KD.TWDK36 t (Certificates.TWDK36.kTwoAt 3 6 CFSG.KD.TWDK36.F CFSG.KD.TWDK36.O
  CFSG.KD.TWDK36.T) 0 8

end
