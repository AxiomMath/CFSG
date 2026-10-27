module

public import Certificates.Data.Kernel.E8Plane.Check
public import Certificates.Kernel.E8Plane.Data

public section

namespace CFSG.KC.E8Plane

open CFSG.KC.E7Plane CFSG.KD.E8Plane

theorem q_check : qB (pk 64 TB) QW RW CJ = true := by decide +kernel

theorem rep1_check : easyB (pk 32 RC) (pk 32 SC) (pk 8 SI) (permP (pk 64 TB) (nthL RW [] 0)) FM1
    WS1 = true := by decide +kernel

theorem rep4_check : easyB (pk 32 RC) (pk 32 SC) (pk 8 SI) (permP (pk 64 TB) (nthL RW [] 1)) FM4
    WS4 = true := by decide +kernel

theorem rep13_fix : fixB' (pk 32 RC) (pk 32 SC) (pk 8 SI) (permP (pk 64 TB) (nthL RW [] 2)) FM13
    FL13 WS13 = true := by decide +kernel

theorem rep13_pairs : pairsB (pk 32 RC) FL13 FC13 WS13 D213 (fstL D313) = true := by decide +kernel

theorem rep13_d2 : allL D213 (d2B (pk 32 RC) (permP (pk 64 TB) (nthL RW [] 2))) = true := by
  decide +kernel

theorem rep13_d3 : allL D313 (fun x => andB (d3B (pk 32 RC) (permP (pk 64 TB) (nthL RW [] 2)) x.1)
    (d3tB (pk 32 RC) (pk 32 SC) (pk 8 SI) (permP (pk 64 TB) (nthL RW [] 2)) x.1 x.2)) = true := by
  decide +kernel

theorem rep40_check : rep4B (pk 32 RC) (pk 32 SC) (pk 8 SI) (permP (pk 64 TB) (nthL RW [] 3)) FM40
    FL40 WS40 = true := by decide +kernel

end CFSG.KC.E8Plane
