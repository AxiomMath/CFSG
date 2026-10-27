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

theorem fix2 : allN 138 (fun m => ptsImg TX MS CM3 M (TT 34) (sliceP PL2 m) (sliceP PL2 m)
    (cntP 8800 m)) = true := by quickRfl

theorem gen2 : allN 6 (fun j => allN 138 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 35 j))
    (sliceP PL2 m) (sliceP (IM j) m) (cntP 8800 m))) = true := by quickRfl

theorem neg_gen2 : Bool.not (ptsImg TX MS CM3 M (TT 35) (sliceP PL2 0) (sliceP PL2 0) 64) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNPt2094

end
