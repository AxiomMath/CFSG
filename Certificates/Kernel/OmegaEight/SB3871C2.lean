module

public import Certificates.Kernel.OmegaEight.SB3871N3
public import Certificates.Kernel.OmegaEight.SB3871KData
public import Certificates.Kernel.OmegaEight.SB3871C1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem korbK_lit : ∀ v < 512, korbK v = korbLit.getD v [] := by
  intro v hv
  have h : ((List.range (8 * 64)).all fun v => decide (korbK v = korbLit.getD v [])) = true := by
    refine all_range_chunks 8 64 fun s hs => ?_
    interval_cases s <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.1 h v (List.mem_range.2 hv))

theorem sKOrb_lit (v : ℕ) : sKOrb[v]! = korbLit.getD v [] := by
  rw [sKOrb_get]
  by_cases hv : v < 512
  · exact korbK_lit v hv
  · rw [korbK, ite_eq_right hv, List.getD_eq_default _ _ (by
      rw [(by decide +kernel : korbLit.length = 512)]; omega)]

set_option maxHeartbeats 0 in
theorem check2 : sAutCheck2 = true := by
  unfold sAutCheck2
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, check2_n⟩, ?_⟩, ?_⟩ <;>
    simp only [sMul_eqK, sInv_eqK, a9K_lin, sAutData, sMTab_get, sKOrb_lit, sConj,
      a9LinTab_get, a9CoTab_get]
  · refine all_range_chunks 8 64 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · refine all_range_chunks 2 64 fun s hs => ?_
    interval_cases s <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end CertificateChecks.KernelO8.SB3871

end
