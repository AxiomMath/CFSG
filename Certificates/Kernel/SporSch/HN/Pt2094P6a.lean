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

@[expose] noncomputable def f6c (m : Nat) : Bool := ptsImg TX MS CM3 M (TT 21) (sliceP PL6 m)
  (sliceP PL6 m) (cntP 8800 m)

@[expose] noncomputable def g6ac (j m : Nat) : Bool := ptsImg TX MS CM3 M (TT (Nat.add 22 j))
  (sliceP PL6 m) (imgP PL6 (SP6 j) m (cntP 8800 m)) (cntP 8800 m)

@[expose] noncomputable def g6ac0 : Nat → Bool := g6ac 0
@[expose] noncomputable def g6ac1 : Nat → Bool := g6ac 1
@[expose] noncomputable def g6ac2 : Nat → Bool := g6ac 2
@[expose] noncomputable def g6ac3 : Nat → Bool := g6ac 3

end CertificateChecks.KernelSporSch.HNPt2094

#kss_each CertificateChecks.KernelSporSch.HNPt2094.F6 CertificateChecks.KernelSporSch.HNPt2094.f6c 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6a0 CertificateChecks.KernelSporSch.HNPt2094.g6ac0 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6a1 CertificateChecks.KernelSporSch.HNPt2094.g6ac1 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6a2 CertificateChecks.KernelSporSch.HNPt2094.g6ac2 138
#kss_each CertificateChecks.KernelSporSch.HNPt2094.G6a3 CertificateChecks.KernelSporSch.HNPt2094.g6ac3 138

namespace CertificateChecks.KernelSporSch.HNPt2094

open CFSG.KC.LL.HNX CFSG.KD.HNPt2094 CFSG.KD.LgHNX CFSG.KC.Enum

theorem fix6 : allN 138 (fun m => ptsImg TX MS CM3 M (TT 21) (sliceP PL6 m) (sliceP PL6 m)
    (cntP 8800 m)) = true := CFSG.KS.PackFld.allN_of_forall F6.all

theorem gen6a : allN 4 (fun j => allN 138 (fun m => ptsImg TX MS CM3 M (TT (Nat.add 22 j))
    (sliceP PL6 m) (imgP PL6 (SP6 j) m (cntP 8800 m)) (cntP 8800 m))) = true := by
  refine CFSG.KS.PackFld.allN_of_forall fun j hj => ?_
  match j, hj with
  | 0, _ => exact CFSG.KS.PackFld.allN_of_forall G6a0.all
  | 1, _ => exact CFSG.KS.PackFld.allN_of_forall G6a1.all
  | 2, _ => exact CFSG.KS.PackFld.allN_of_forall G6a2.all
  | 3, _ => exact CFSG.KS.PackFld.allN_of_forall G6a3.all
  | _ + 4, h => exact absurd h (by omega)

theorem neg_gen6 : Bool.not (ptsImg TX MS CM3 M (TT 22) (sliceP PL6 0) (imgP PL6 (SP6 1) 0 64) 64) =
    true := by quickRfl

end CertificateChecks.KernelSporSch.HNPt2094

end
