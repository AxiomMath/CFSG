module

public import CFSG.GH74.KGroups.CoverM23Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M23 CFSG.Certificates.Kernel.PkEnum
  CFSG.Sporadic.Schreier

theorem qp_5114K : schP QP = true ∧ orderV QP = 10200960 := by
  constructor <;> decide +kernel

theorem qe_5114K : schP QE = true ∧ orderV QE = 16 := by
  constructor <;> decide +kernel

theorem sq_5114K : sqOneCheck (elemsV QE) = true := by
  decide +kernel

theorem conj_5114K : conjWordsCheck [m23PermA, m23PermB] eg0 cws (elemsV QE) = true := by
  decide +kernel

theorem indep_5114K : indepCheck eg0 eg1 eg2 = true := by
  decide +kernel

theorem le_5114K : (QE.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

theorem sift_5114K : siftP QE eg0 0 = true ∧ siftP QE eg1 0 = true ∧ siftP QE eg2 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem neg5114K : orderV QP ≠ 443520 := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
