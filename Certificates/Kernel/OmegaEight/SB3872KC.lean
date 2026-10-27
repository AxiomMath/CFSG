module

public import Certificates.Kernel.OmegaEight.SB3872K
public import Certificates.Kernel.OmegaEight.SBChunks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8
  CertificateChecks.KernelO8.SB3871

set_option maxHeartbeats 0 in
theorem cls_check : kClassOK mulK invK sGens 65536 sClsLit = true := by
  unfold kClassOK
  rw [kInv_eq, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by decide +kernel, ?_⟩, by decide +kernel⟩
  rw [← chunks_flatten 8 17 sClsLit (by decide +kernel)]
  refine all_blocks _ _ fun s hs => ?_
  rw [chunks_length] at hs
  interval_cases s <;> decide +kernel

theorem repsC_eq : kRepsC sClsLit 4 = rLit := by decide +kernel

theorem kill_check : sKill = true := by
  unfold sKill groupKillC
  simp only [sMul_eqK, sInv_eqK, kInv_eq, kOrd4_eq, repsC_eq, killAtC_eq, Bool.and_eq_true,
    List.all_eq_true]
  exact ⟨⟨⟨kill_inv, cls_check⟩, kill_chi⟩, kill_at⟩

end CertificateChecks.KernelO8.SB3872

end
