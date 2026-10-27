module

public import Certificates.Kernel.OmegaEight.SB3871N1
public import Certificates.Kernel.OmegaEight.SB3871N2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem nStep8 : ∀ s < (nBlocks 8).length, nStepOK 8 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 8).length = 128)] at hs
  refine nStepOK_of_B (by norm_num) ?_
  interval_cases s <;> decide +kernel

theorem nSearch_eq : nSearch 9 7 sAutData.M sAutData.cb sAutData.olen = (nSt 9).map Prod.fst := by
  have hlen : ∀ i < 9, (nLv (i + 1)).length = (nBlocks i).length := by
    intro i hi
    interval_cases i <;> decide +kernel
  have hstep : ∀ i < 9, ∀ s < (nBlocks i).length, nStepOK i s = true := by
    intro i hi
    interval_cases i
    exacts [nStep0, nStep1, nStep2, nStep3, nStep4, nStep5, nStep6, nStep7, nStep8]
  rw [M_eq, cb_eq, olen_eq, nSearch, nStates_eq hlen hstep 9 le_rfl]

set_option maxHeartbeats 0 in
theorem check2_n : ((nSearch 9 7 sAutData.M sAutData.cb sAutData.olen).all fun V =>
    (List.range 8).any fun k => (List.range 128).any fun e =>
      (List.range 9).all fun i => V.getD i 0 == sAutData.M e (sAutData.P k i)) = true := by
  rw [nSearch_eq, List.all_map, nSt]
  refine all_blocks _ _ fun s hs => ?_
  rw [(by decide +kernel : (nBlocks 9).length = 64)] at hs
  rw [M_eq]
  simp only [sAutData]
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
