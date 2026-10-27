module

public import Certificates.Kernel.TWLK.D39
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLK39

open Certificates.TWLK

theorem roots : kRootsOK 3 9 RF = true := by decide +kernel

theorem cover : kCover 9 S T = true := by decide +kernel

theorem lenS : S.length = 20 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel

theorem neg_roots : (!kRootsOK 3 9 RF.tail) = true := by decide +kernel

theorem neg_cover : (!kCover 9 S T.tail) = true := by decide +kernel

theorem neg_cut : (!kPat2At 3 9 RF (kRT8 3 9 H E)
    (T.map fun e => (e.1, e.2.1, e.2.2.dropLast)) 0) = true := by
  decide +kernel

theorem neg_idx : (!kPat2At 3 9 RF (kRT8 3 9 H E)
    (T.map fun e => (e.1, e.2.1, e.2.2.map fun c => (c.1, c.2 + 100))) 0) = true := by
  decide +kernel

theorem neg_hk : (!kPat1At 3 9 RF (kRT8 3 9 (H.map fun h => (h.1, h.2.tail)) E) S 0) = true := by
  decide +kernel

theorem neg_e8 : (!kPat1At 3 9 RF
    (kRT8 3 9 H (E.map fun w => (w.1, w.2.1.map (fun u => (u.1, 0 :: u.2)), w.2.2))) S 3) =
      true := by
  decide +kernel

theorem neg_e6 : (!kPat1At 3 9 RF (kRT8 3 9 H E)
    (S.map fun e => (e.1, e.2.1, e.2.2.map fun c => (if c.1 = 4 then 3 else c.1, c.2))) 3) =
      true := by
  decide +kernel

end CFSG.KD.TWLK39

#kc_each CFSG.KD.TWLK39 l39s
  (Certificates.TWLK.kPat1At 3 9 CFSG.KD.TWLK39.RF
    (Certificates.TWLK.kRT8 3 9 CFSG.KD.TWLK39.H CFSG.KD.TWLK39.E) CFSG.KD.TWLK39.S) 0 20

#kc_each CFSG.KD.TWLK39 l39t
  (Certificates.TWLK.kPat2At 3 9 CFSG.KD.TWLK39.RF
    (Certificates.TWLK.kRT8 3 9 CFSG.KD.TWLK39.H CFSG.KD.TWLK39.E) CFSG.KD.TWLK39.T) 0 8

end
