module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H0

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W0 : L2EW where
  vS := vSArr
  RW := rw0
  IV := invRows0.flatten.map vecK
  Rs := rs0
  C3 := cent0_4.2.1
  O3 := recMB (t1Mul (s2F 0) (s2Z 0)) (t1Inv (s2F 0) (s2Z 0)) t1Gens 32 3
  LW := lw0

namespace C0

theorem hmul : t1Mul (s2F 0) (s2Z 0) = MK 0 16 0 := by
  rw [s2F_eq (k := 0) (m := 16) rfl rfl]
  exact t1Mul_eq 0 V0.hw V0.hl

theorem hinv : t1Inv (s2F 0) (s2Z 0) = IK 0 16 0 := by
  rw [s2F_eq (k := 0) (m := 16) rfl rfl]
  exact t1Inv_eq 0 V0.hw V0.hl

theorem hF1 (c : ℕ) : (s2F 0)[c]! = FK 0 16 c := by
  rw [s2F_eq (k := 0) (m := 16) rfl rfl]
  exact congrFun (sFTab_eq V0.hw V0.hl) c

theorem iota : l2eIotaOK 0 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V0.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK]
  decide +kernel

theorem enum : l2eEnumOK 0 (t1Vec vSArr) rs0 cent0_4.2.1
    (recMB (t1Mul (s2F 0) (s2Z 0)) (t1Inv (s2F 0) (s2Z 0)) t1Gens 32 3) lw0 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V0.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C0

theorem surv0 : l2eSurvOK 0 W0 = true := by
  unfold l2eSurvOK
  dsimp only [W0]
  rw [hvS, char0, C0.iota, C0.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
