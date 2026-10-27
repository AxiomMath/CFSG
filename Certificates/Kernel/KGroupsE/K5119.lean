module

public import CFSG.GH74.KGroups.L28TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L28 CFSG.Certificates.Kernel.PkEnum

theorem qs_5119K : schP QS = true ∧ orderV QS = 8 := by
  constructor <;> decide +kernel

theorem comm_5119K : commCheck (elemsV QS) = true := by
  decide +kernel

theorem pow_5119K : ((elemsV QA).all fun g => bif decide (g ^ 8 = 1) then siftP QP g 0 else true)
    = true := by
  decide +kernel

theorem le_5119K : (QS.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

theorem neg5119K : ((elemsV QA).all fun g => siftP QP g 0) = false := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
