module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H3

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W3 : L2EW where
  vS := vSArr
  RW := rw3
  IV := invRows30.flatten.map vecK
  Rs := rs3
  C3 := cent3_4.2.1
  O3 := recMB (t1Mul (s2F 3) (s2Z 3)) (t1Inv (s2F 3) (s2Z 3)) t1Gens 32 3
  LW := lw3

namespace C3

theorem hmul : t1Mul (s2F 3) (s2Z 3) = MK 0 31 0 := by
  rw [s2F_eq (k := 0) (m := 31) rfl rfl]
  exact t1Mul_eq 0 V3.hw V3.hl

theorem hinv : t1Inv (s2F 3) (s2Z 3) = IK 0 31 0 := by
  rw [s2F_eq (k := 0) (m := 31) rfl rfl]
  exact t1Inv_eq 0 V3.hw V3.hl

theorem hF1 (c : ℕ) : (s2F 3)[c]! = FK 0 31 c := by
  rw [s2F_eq (k := 0) (m := 31) rfl rfl]
  exact congrFun (sFTab_eq V3.hw V3.hl) c

theorem iota : l2eIotaOK 3 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V3.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK]
  decide +kernel

theorem enum : l2eEnumOK 3 (t1Vec vSArr) rs3 cent3_4.2.1
    (recMB (t1Mul (s2F 3) (s2Z 3)) (t1Inv (s2F 3) (s2Z 3)) t1Gens 32 3) lw3 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V3.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C3

theorem surv3 : l2eSurvOK 3 W3 = true := by
  unfold l2eSurvOK
  dsimp only [W3]
  rw [hvS, char3, C3.iota, C3.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
