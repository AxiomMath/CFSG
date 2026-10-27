module

public import Certificates.Kernel.OmegaEight.SB3871C1
public import Certificates.Kernel.OmegaEight.SB3871Data
public import Certificates.Kernel.OmegaEight.SB3871Blocks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem sInvList_eq : sInvList = sInvListLit := by
  unfold sInvList
  rw [sMul_eqK]
  decide +kernel

theorem sInvRows_eq : sInvListLit = sInvRows.flatten := by
  decide +kernel

theorem sYRows_eq : sYLit = sYRows.flatten := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sY_eq : sY = sYLit := by
  unfold sY sNinv sInvRec
  rw [sInvList_eq, sMul_eqK, sInv_eqK, sYRows_eq]
  conv_lhs => rw [sInvRows_eq]
  refine filter_blocks _ _ _ (by decide +kernel) fun s hs => ?_
  rw [(by decide +kernel : sInvRows.length = 15)] at hs
  rw [← sInvRows_eq]
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem check4 : sAutCheck4 = true := by
  unfold sAutCheck4 sInvRec
  rw [sInvList_eq, sY_eq]
  simp only [sMul_eqK, sInv_eqK, a9K_lin, a9K_co, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [sInvRows_eq]
    refine all_blocks _ _ fun s hs => ?_
    rw [(by decide +kernel : sInvRows.length = 15)] at hs
    interval_cases s <;> decide +kernel
  · refine all_range_chunks 2048 32 fun s hs => ?_
    interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
