module

public import Certificates.Kernel.SporSch.HN.Pt2094Data
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXChunk
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KD.HNPt2094 CFSG.KD.LgHNX CFSG.KC.Enum

@[expose] noncomputable def g6bc (j m : Nat) : Bool := ptsImg TX MS CM3 M (TT (Nat.add 26 j))
  (sliceP PL6 m) (imgP PL6 (SP6 (Nat.add 4 j)) m (cntP 8800 m)) (cntP 8800 m)

@[expose] noncomputable def g6bc0 : Nat → Bool := g6bc 0
@[expose] noncomputable def g6bc1 : Nat → Bool := g6bc 1
@[expose] noncomputable def g6bc2 : Nat → Bool := g6bc 2
@[expose] noncomputable def g6bc3 : Nat → Bool := g6bc 3

end CertificateChecks.KernelSporSch.HNPt2094

#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6b0 CertificateChecks.KernelSporSch.HNPt2094.g6bc0 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6b1 CertificateChecks.KernelSporSch.HNPt2094.g6bc1 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6b2 CertificateChecks.KernelSporSch.HNPt2094.g6bc2 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6b3 CertificateChecks.KernelSporSch.HNPt2094.g6bc3 138

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KD.HNPt2094 CFSG.KD.LgHNX CFSG.KC.Enum

theorem gen6b : allN 4 (fun j => allN 138 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 26 j))
    (sliceP PL6 m) (imgP PL6 (SP6 (Nat.add 4 j)) m (cntP 8800 m)) (cntP 8800 m))) = true := by
  refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
  match j, hj with
  | 0, _ => exact CFSG.KS.PackFld.allN_of_forall G6b0.all
  | 1, _ => exact CFSG.KS.PackFld.allN_of_forall G6b1.all
  | 2, _ => exact CFSG.KS.PackFld.allN_of_forall G6b2.all
  | 3, _ => exact CFSG.KS.PackFld.allN_of_forall G6b3.all
  | _ + 4, h => exact absurd h (by omega)

end CertificateChecks.KernelSporSch.HNPt2094

end
