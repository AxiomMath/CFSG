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

theorem gen6c : allN 4 (fun j => allN 138 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 30 j))
    (sliceP PL6 m) (imgP PL6 (SP6 (Nat.add 8 j)) m (cntP 8800 m)) (cntP 8800 m))) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNPt2094

end
