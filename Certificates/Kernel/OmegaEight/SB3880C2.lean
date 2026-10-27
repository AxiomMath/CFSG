module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H2

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W2 : L2EW where
  vS := vSArr
  RW := rw2
  IV := invRows20.flatten.map vecK
  Rs := rs2
  C3 := cent2_4.2.1
  O3 := recMB (t1Mul (s2F 2) (s2Z 2)) (t1Inv (s2F 2) (s2Z 2)) t1Gens 32 3
  LW := lw2

namespace C2

theorem hmul : t1Mul (s2F 2) (s2Z 2) = MK 0 26 0 := by
  rw [s2F_eq (k := 0) (m := 26) rfl rfl]
  exact t1Mul_eq 0 V2.hw V2.hl

theorem hinv : t1Inv (s2F 2) (s2Z 2) = IK 0 26 0 := by
  rw [s2F_eq (k := 0) (m := 26) rfl rfl]
  exact t1Inv_eq 0 V2.hw V2.hl

theorem hF1 (c : ℕ) : (s2F 2)[c]! = FK 0 26 c := by
  rw [s2F_eq (k := 0) (m := 26) rfl rfl]
  exact congrFun (sFTab_eq V2.hw V2.hl) c

theorem iota : l2eIotaOK 2 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V2.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK]
  decide +kernel

theorem enum : l2eEnumOK 2 (t1Vec vSArr) rs2 cent2_4.2.1
    (recMB (t1Mul (s2F 2) (s2Z 2)) (t1Inv (s2F 2) (s2Z 2)) t1Gens 32 3) lw2 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V2.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C2

theorem surv2 : l2eSurvOK 2 W2 = true := by
  unfold l2eSurvOK
  dsimp only [W2]
  rw [hvS, char2, C2.iota, C2.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
