module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H4

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W4 : L2EW where
  vS := vSArr
  RW := rw4
  IV := invRows33.flatten.map vecK
  Rs := rs4
  C3 := cent4_4.2.1
  O3 := recMB (t1Mul (s2F 4) (s2Z 4)) (t1Inv (s2F 4) (s2Z 4)) t1Gens 32 3
  LW := lw4

namespace C4

theorem hmul : t1Mul (s2F 4) (s2Z 4) = MK 1 16 24 := by
  rw [s2F_eq (k := 1) (m := 16) rfl rfl]
  exact t1Mul_eq 24 V4.hw V4.hl

theorem hinv : t1Inv (s2F 4) (s2Z 4) = IK 1 16 24 := by
  rw [s2F_eq (k := 1) (m := 16) rfl rfl]
  exact t1Inv_eq 24 V4.hw V4.hl

theorem hF1 (c : ℕ) : (s2F 4)[c]! = FK 1 16 c := by
  rw [s2F_eq (k := 1) (m := 16) rfl rfl]
  exact congrFun (sFTab_eq V4.hw V4.hl) c

theorem iota : l2eIotaOK 4 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V4.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK]
  decide +kernel

theorem enum : l2eEnumOK 4 (t1Vec vSArr) rs4 cent4_4.2.1
    (recMB (t1Mul (s2F 4) (s2Z 4)) (t1Inv (s2F 4) (s2Z 4)) t1Gens 32 3) lw4 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V4.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C4

theorem surv4 : l2eSurvOK 4 W4 = true := by
  unfold l2eSurvOK
  dsimp only [W4]
  rw [hvS, char4, C4.iota, C4.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
