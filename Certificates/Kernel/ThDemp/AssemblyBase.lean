
module

public import CFSG.Certificates.Kernel.ThDemp.SoundBase
public import CFSG.Sporadic.Th.SetupBase
public import Certificates.Kernel.ThDemp.Data
import Certificates.Kernel.ThDemp.Slp
import Certificates.Kernel.ThDemp.Shape
import Certificates.Kernel.ThDemp.Lev
import Certificates.Kernel.ThDemp.Res0
import Certificates.Kernel.ThDemp.Res1
import Certificates.Kernel.ThDemp.Res2
import Certificates.Kernel.ThDemp.Res3
import Certificates.Kernel.ThDemp.Res4
import Certificates.Kernel.ThDemp.Res5
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Checks2.Seed_S

@[expose] public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.KC.Th CFSG.Certificates.ThDemp CFSG.Sporadic.Th

theorem andB_tt {x y : Bool} (hx : x = true) (hy : y = true) : andB x y = true := by
  subst hx
  exact hy

theorem demp_chk : dempChk dempData = true :=
  andB_tt slp_ok (andB_tt shape_ok (andB_tt levels_ok (andB_tt res0_ok (andB_tt res1_ok
    (andB_tt res2_ok (andB_tt res3_ok (andB_tt res4_ok res5_ok)))))))

theorem rd_zero : BigS.regAt dempData.rd 0 = 1 := by decide +kernel

theorem pkMat_SA :
    CFSG.KC.Th.Spec.pkMat dempData.SA = matA := by
  rw [show dempData.SA = CFSG.KD.ThSeed.SA from rfl,
    (CFSG.KC.Th.Spec.decOK_sound CFSG.KD.ThSeed.dA).2, ← CFSG.KD.ThSeed.LA_eq,
    rowsMatrix_rowsOf_seedA]

theorem pkMat_SB :
    CFSG.KC.Th.Spec.pkMat dempData.SB = matB := by
  rw [show dempData.SB = CFSG.KD.ThSeed.SB from rfl,
    (CFSG.KC.Th.Spec.decOK_sound CFSG.KD.ThSeed.dB).2, ← CFSG.KD.ThSeed.LB_eq,
    rowsMatrix_rowsOf_seedB]

end CertificateChecks.KernelThDemp

end
