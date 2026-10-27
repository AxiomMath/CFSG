module

public import Certificates.Kernel.TWLK.D55
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWLK55

open Certificates.TWLK

theorem roots : kRootsOK 5 5 RF = true := by decide +kernel

theorem cover : kCover 5 S T = true := by decide +kernel

theorem lenS : S.length = 12 := by decide +kernel

theorem lenT : T.length = 8 := by decide +kernel

theorem neg_roots : (!kRootsOK 5 5 RF.tail) = true := by decide +kernel

theorem neg_cover : (!kCover 5 S T.tail) = true := by decide +kernel

theorem neg_cut : (!kPat1At 5 5 RF (kRTPZ 5 5 H Z)
    (S.map fun e => (e.1, e.2.1, e.2.2.dropLast)) 0) = true := by
  decide +kernel

theorem neg_idx : (!kPat1At 5 5 RF (kRTPZ 5 5 H Z)
    (S.map fun e => (e.1, e.2.1, e.2.2.map fun c => (c.1, c.2 + 100))) 0) = true := by
  decide +kernel

theorem neg_hk : (!kPat1At 5 5 RF (kRTPZ 5 5 (H.map fun h => (h.1, h.2.tail)) Z) S 0) = true := by
  decide +kernel

theorem neg_pz_lcm : (!kPat2At 5 5 RF
    (kRTPZ 5 5 H (Z.map fun z => (z.1, z.2.1.dropLast, z.2.2))) T 0) = true := by
  decide +kernel

theorem neg_pz_cen : (!kPat2At 5 5 RF
    (kRTPZ 5 5 H (Z.map fun z => (z.1, z.2.1, []))) T 0) = true := by
  decide +kernel

theorem neg_pz_tree : (!kPat2At 5 5 RF (kRTPZ 5 5 H (Z.map fun z =>
    if z.2.2.isEmpty then (z.1, z.2.1.map (fun s => (s.1, s.2.dropLast)), z.2.2) else z)) T 0) =
      true := by
  decide +kernel

theorem neg_pz_kind : (!kPat2At 5 5 RF (kRTPZ 5 5 H Z)
    (T.map fun e => (e.1, e.2.1, e.2.2.map fun c => (if c.1 = 2 then 1 else c.1, c.2))) 0) =
      true := by
  decide +kernel

end CFSG.KD.TWLK55

#kc_each CFSG.KD.TWLK55 l55s
  (Certificates.TWLK.kPat1At 5 5 CFSG.KD.TWLK55.RF
    (Certificates.TWLK.kRTPZ 5 5 CFSG.KD.TWLK55.H CFSG.KD.TWLK55.Z) CFSG.KD.TWLK55.S) 0 12

#kc_each CFSG.KD.TWLK55 l55t
  (Certificates.TWLK.kPat2At 5 5 CFSG.KD.TWLK55.RF
    (Certificates.TWLK.kRTPZ 5 5 CFSG.KD.TWLK55.H CFSG.KD.TWLK55.Z) CFSG.KD.TWLK55.T) 0 8

end
