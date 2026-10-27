module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H6

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W6 : L2EW where
  vS := vSArr
  RW := rw6
  IV := invRows53.flatten.map vecK
  Rs := rs6
  C3 := cent6_4.2.1
  O3 := recMB (t1Mul (s2F 6) (s2Z 6)) (t1Inv (s2F 6) (s2Z 6)) t1Gens 32 3
  LW := lw6

namespace C6

theorem hmul : t1Mul (s2F 6) (s2Z 6) = MK 1 26 24 := by
  rw [s2F_eq (k := 1) (m := 26) rfl rfl]
  exact t1Mul_eq 24 V6.hw V6.hl

theorem hinv : t1Inv (s2F 6) (s2Z 6) = IK 1 26 24 := by
  rw [s2F_eq (k := 1) (m := 26) rfl rfl]
  exact t1Inv_eq 24 V6.hw V6.hl

theorem hF1 (c : ℕ) : (s2F 6)[c]! = FK 1 26 c := by
  rw [s2F_eq (k := 1) (m := 26) rfl rfl]
  exact congrFun (sFTab_eq V6.hw V6.hl) c

theorem iota : l2eIotaOK 6 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V6.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK]
  decide +kernel

theorem enum : l2eEnumOK 6 (t1Vec vSArr) rs6 cent6_4.2.1
    (recMB (t1Mul (s2F 6) (s2Z 6)) (t1Inv (s2F 6) (s2Z 6)) t1Gens 32 3) lw6 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V6.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C6

theorem surv6 : l2eSurvOK 6 W6 = true := by
  unfold l2eSurvOK
  dsimp only [W6]
  rw [hvS, char6, C6.iota, C6.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
