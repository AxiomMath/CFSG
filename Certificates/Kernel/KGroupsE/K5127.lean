module

public import CFSG.GH74.KGroups.M22Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.M22 CFSG.Certificates.Kernel.PkEnum
  CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

theorem qp_5127K : schP QP = true ∧ orderV QP = 443520 := by
  constructor <;> decide +kernel

theorem qe_5127K : schP QE = true ∧ orderV QE = 16 := by
  constructor <;> decide +kernel

theorem sq_5127K : sqOneCheck (elemsV QE) = true := by
  decide +kernel

theorem conj_5127K : conjWordsCheck [m22gA, m22gB] eg0 cws (elemsV QE) = true := by
  decide +kernel

theorem indep_5127K : indepCheck eg0 eg1 eg2 = true := by
  decide +kernel

theorem le_5127K : (QE.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

theorem sift_5127K : siftP QE eg0 0 = true ∧ siftP QE eg1 0 = true ∧ siftP QE eg2 0 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem neg5127K : orderV QP ≠ 887040 := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
