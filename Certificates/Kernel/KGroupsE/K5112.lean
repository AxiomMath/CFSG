
module

public import CFSG.GH74.KGroups.CoverL34Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem qe_5112K : schP QE = true ∧ orderV QE = 16 := by
  constructor <;> decide +kernel

theorem sq_5112K : sqOneCheck (elemsV QE) = true := by
  decide +kernel

theorem conj_5112K : conjWordsCheck [PA, PB] eg0 cws (elemsV QE) = true := by
  decide +kernel

theorem indep_5112K : indepCheck eg0 eg1 eg2 = true := by
  decide +kernel

theorem le_5112K : (QE.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

theorem sift_5112K : siftP QE eg0 0 = true ∧ siftP QE eg1 0 = true ∧ siftP QE eg2 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem neg5112K : orderV QE ≠ 32 := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
