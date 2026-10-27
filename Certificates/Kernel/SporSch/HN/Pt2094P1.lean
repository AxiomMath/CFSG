module

public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXChunk
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KD.HNPt2094 CFSG.KD.LgHNX CFSG.KC.Enum

theorem fix1 : allN 19 (fun m => ptsImg TX MS CM3 M (TT 0) (sliceP PL1 m) (sliceP PL1 m)
    (cntP 1156 m)) = true := by quickRfl

theorem gen1 : allN 9 (fun j => allN 19 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 1 j))
    (sliceP PL1 m) (imgP PL1 (SP1 j) m (cntP 1156 m)) (cntP 1156 m))) = true := by quickRfl

theorem fix4 : allN 13 (fun m => ptsImg TX MS CM3 M (TT 20) (sliceP PL4 m) (sliceP PL4 m)
    (cntP 800 m)) = true := by quickRfl

theorem gen4 : allN 10 (fun j => allN 13 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 10 j))
    (sliceP PL4 m) (imgP PL4 (SP4 j) m (cntP 800 m)) (cntP 800 m))) = true := by quickRfl

theorem gen4c : allN 13 (fun m => ptsImg TX MS CM3 M (TT 0) (sliceP PL4 m)
    (imgP PL4 (SP4 10) m (cntP 800 m)) (cntP 800 m)) = true := by quickRfl

theorem neg_gen1 : Bool.not (ptsImg TX MS CM3 M (TT 1) (sliceP PL1 0) (imgP PL1 (SP1 1) 0 64) 64) =
    true := by quickRfl

theorem neg_fix4 : Bool.not (ptsImg TX MS CM3 M (TT 21) (sliceP PL4 0) (sliceP PL4 0) 64) = true :=
  by quickRfl

end CertificateChecks.KernelSporSch.HNPt2094

end
