module

public import CFSG.GH74.KGroups.U33TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Certificates.Kernel.PkEnum

theorem qs_5134K : schP QS = true ∧ orderV QS = 32 := by
  constructor <;> decide +kernel

theorem inv_5134K : invConjCheck (elemsV QP) t0 = true := by
  decide +kernel

theorem small_5134K : smallCheck (elemsV QS) s0 = true := by
  decide +kernel

theorem le_5134K : (QS.original.toList.all fun g => siftP QP g 0) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
