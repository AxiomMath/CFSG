module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H5

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W5 : L2EW where
  vS := vSArr
  RW := rw5
  IV := invRows43.flatten.map vecK
  Rs := rs5
  C3 := cent5_4.2.1
  O3 := recMB (t1Mul (s2F 5) (s2Z 5)) (t1Inv (s2F 5) (s2Z 5)) t1Gens 32 3
  LW := lw5

namespace C5

theorem hmul : t1Mul (s2F 5) (s2Z 5) = MK 1 21 24 := by
  rw [s2F_eq (k := 1) (m := 21) rfl rfl]
  exact t1Mul_eq 24 V5.hw V5.hl

theorem hinv : t1Inv (s2F 5) (s2Z 5) = IK 1 21 24 := by
  rw [s2F_eq (k := 1) (m := 21) rfl rfl]
  exact t1Inv_eq 24 V5.hw V5.hl

theorem hF1 (c : ℕ) : (s2F 5)[c]! = FK 1 21 c := by
  rw [s2F_eq (k := 1) (m := 21) rfl rfl]
  exact congrFun (sFTab_eq V5.hw V5.hl) c

theorem iota : l2eIotaOK 5 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V5.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK]
  decide +kernel

theorem enum : l2eEnumOK 5 (t1Vec vSArr) rs5 cent5_4.2.1
    (recMB (t1Mul (s2F 5) (s2Z 5)) (t1Inv (s2F 5) (s2Z 5)) t1Gens 32 3) lw5 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V5.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C5

theorem surv5 : l2eSurvOK 5 W5 = true := by
  unfold l2eSurvOK
  dsimp only [W5]
  rw [hvS, char5, C5.iota, C5.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
