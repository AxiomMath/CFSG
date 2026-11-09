module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H7

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W7 : L2EW where
  vS := vSArr
  RW := rw7
  IV := invRows63.flatten.map vecK
  Rs := rs7
  C3 := cent7_4.2.1
  O3 := recMB (t1Mul (s2F 7) (s2Z 7)) (t1Inv (s2F 7) (s2Z 7)) t1Gens 32 3
  LW := lw7

private theorem all_range_65536 {P : ℕ → Bool}
    (h : ∀ s < 8, (List.range' (8192 * s) 8192).all P = true) : (List.range 65536).all P = true :=
  all_range_chunks 8192 8 h

namespace C7

theorem hmul : t1Mul (s2F 7) (s2Z 7) = MK 1 31 24 := by
  rw [s2F_eq (k := 1) (m := 31) rfl rfl]
  exact t1Mul_eq 24 V7.hw V7.hl

theorem hinv : t1Inv (s2F 7) (s2Z 7) = IK 1 31 24 := by
  rw [s2F_eq (k := 1) (m := 31) rfl rfl]
  exact t1Inv_eq 24 V7.hw V7.hl

theorem hF1 (c : ℕ) : (s2F 7)[c]! = FK 1 31 c := by
  rw [s2F_eq (k := 1) (m := 31) rfl rfl]
  exact congrFun (sFTab_eq V7.hw V7.hl) c

theorem iota : l2eIotaOK 7 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V7.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK,
    Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · refine all_range_65536 fun s hs => ?_
    rcases s with _ | _ | _ | _ | _ | _ | _ | _ | s
    all_goals first | omega | decide +kernel
  all_goals decide +kernel

theorem enum : l2eEnumOK 7 (t1Vec vSArr) rs7 cent7_4.2.1
    (recMB (t1Mul (s2F 7) (s2Z 7)) (t1Inv (s2F 7) (s2Z 7)) t1Gens 32 3) lw7 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V7.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C7

theorem surv7 : l2eSurvOK 7 W7 = true := by
  unfold l2eSurvOK
  dsimp only [W7]
  rw [hvS, char7, C7.iota, C7.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
