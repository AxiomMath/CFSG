module

public import Certificates.Kernel.TWLK.D36
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLK36

open Certificates.TWLK

theorem frame : kFrameOK 3 6 FV FW = true := by decide +kernel

theorem roots : kRootsOK 3 6 RF = true := by decide +kernel

theorem cover : kCover 6 S T = true := by decide +kernel

theorem lenS : S.length = 14 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel

theorem neg_frame_dup : (!kFrameOK 3 6 FV (FW.take 1 ++ FW.dropLast)) = true := by decide +kernel

theorem neg_frame_len : (!kFrameOK 3 6 FV FW.tail) = true := by decide +kernel

theorem neg_frame_gen : (!kFrameOK 3 6 FV (FW.map (5 :: ·))) = true := by decide +kernel

theorem neg_roots : (!kRootsOK 3 6 RF.tail) = true := by decide +kernel

theorem neg_cover : (!kCover 6 S T.tail) = true := by decide +kernel

theorem neg_cut : (!kPat2At 3 6 RF (kRT6 3 6 H Z F)
    (T.map fun e => (e.1, e.2.1, e.2.2.dropLast)) 0) = true := by
  decide +kernel

theorem neg_idx : (!kPat2At 3 6 RF (kRT6 3 6 H Z F)
    (T.map fun e => (e.1, e.2.1, e.2.2.map fun c => (c.1, c.2 + 100))) 0) = true := by
  decide +kernel

theorem neg_hk : (!kPat1At 3 6 RF (kRT6 3 6 (H.map fun h => (h.1, h.2.tail)) Z F) S 0) = true := by
  decide +kernel

theorem neg_pz : (!kPat1At 3 6 RF
    (kRT6 3 6 H (Z.map fun z => (z.1, z.2.1.map (fun s => (s.1.take 1, s.2)), z.2.2)) F) S 3) =
      true := by
  decide +kernel

theorem neg_e6 : (!kPat1At 3 6 RF
    (kRT6 3 6 H Z (F.map fun w => (w.1, w.2.1.map (fun u => (u.1, 0 :: u.2)), w.2.2))) S 3) =
      true := by
  decide +kernel

theorem neg_cox : (!kPat1At 3 6 RF (kRT6 3 6 H Z (F.map fun w => (w.1.reverse, w.2))) S 3) =
    true := by
  decide +kernel

theorem neg_orbit : (!kPat1At 3 6 RF
    (kRT6 3 6 H Z (F.map fun w => (w.1, w.2.1, w.2.2.1, w.2.2.2.map fun e => (0, e.2)))) S 3) =
      true := by
  decide +kernel

theorem neg_e8 : (!kPat1At 3 6 RF (kRT6 3 6 H Z F)
    (S.map fun e => (e.1, e.2.1, e.2.2.map fun c => (if c.1 = 3 then 4 else c.1, c.2))) 3) =
      true := by
  decide +kernel

end CFSG.KD.TWLK36

#kc_each CFSG.KD.TWLK36 l36s
  (Certificates.TWLK.kPat1At 3 6 CFSG.KD.TWLK36.RF
    (Certificates.TWLK.kRT6 3 6 CFSG.KD.TWLK36.H CFSG.KD.TWLK36.Z CFSG.KD.TWLK36.F)
    CFSG.KD.TWLK36.S) 0 14

#kc_each CFSG.KD.TWLK36 l36t
  (Certificates.TWLK.kPat2At 3 6 CFSG.KD.TWLK36.RF
    (Certificates.TWLK.kRT6 3 6 CFSG.KD.TWLK36.H CFSG.KD.TWLK36.Z CFSG.KD.TWLK36.F)
    CFSG.KD.TWLK36.T) 0 8

end
