module

public import Certificates.Kernel.OmegaEight.SB3880BC
public import Certificates.Kernel.OmegaEight.SB3880H1

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelO8.SB3880

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873
  CertificateChecks.KernelO8.SB3884

@[expose] noncomputable def W1 : L2EW where
  vS := vSArr
  RW := rw1
  IV := invRows10.flatten.map vecK
  Rs := rs1
  C3 := cent1_4.2.1
  O3 := recMB (t1Mul (s2F 1) (s2Z 1)) (t1Inv (s2F 1) (s2Z 1)) t1Gens 32 3
  LW := lw1

private theorem all_range_65536 {P : ℕ → Bool}
    (h : ∀ s < 8, (List.range' (8192 * s) 8192).all P = true) : (List.range 65536).all P = true :=
  all_range_chunks 8192 8 h

namespace C1

theorem hmul : t1Mul (s2F 1) (s2Z 1) = MK 0 21 0 := by
  rw [s2F_eq (k := 0) (m := 21) rfl rfl]
  exact t1Mul_eq 0 V1.hw V1.hl

theorem hinv : t1Inv (s2F 1) (s2Z 1) = IK 0 21 0 := by
  rw [s2F_eq (k := 0) (m := 21) rfl rfl]
  exact t1Inv_eq 0 V1.hw V1.hl

theorem hF1 (c : ℕ) : (s2F 1)[c]! = FK 0 21 c := by
  rw [s2F_eq (k := 0) (m := 21) rfl rfl]
  exact congrFun (sFTab_eq V1.hw V1.hl) c

theorem iota : l2eIotaOK 1 (t1Vec vSArr) = true := by
  unfold l2eIotaOK l2eIL l2eIW
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V1.hio, s2InSp, vec_get, cb_eq, a9K_co, a9K_lin, sMul_eqK,
    Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · refine all_range_65536 fun s hs => ?_
    rcases s with _ | _ | _ | _ | _ | _ | _ | _ | s
    all_goals first | omega | decide +kernel
  all_goals decide +kernel

theorem enum : l2eEnumOK 1 (t1Vec vSArr) rs1 cent1_4.2.1
    (recMB (t1Mul (s2F 1) (s2Z 1)) (t1Inv (s2F 1) (s2Z 1)) t1Gens 32 3) lw1 = true := by
  unfold l2eEnumOK l2eRecsOK l2eCentOK l2eLeafOK l2eActOK l2eActR
  dsimp only
  rw [hmul, hinv]
  simp only [iotaTab_get _ V1.hio, s2InSp, vec_get, sFm_eqD, chiS_get, hF1, s2B]
  decide +kernel

end C1

theorem surv1 : l2eSurvOK 1 W1 = true := by
  unfold l2eSurvOK
  dsimp only [W1]
  rw [hvS, char1, C1.iota, C1.enum]
  rfl

end CertificateChecks.KernelO8.SB3880

end
