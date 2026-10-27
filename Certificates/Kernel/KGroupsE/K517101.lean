module

public import Certificates.Data.S7SocL33
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups Certificates.S7SocQ8 Certificates.S7SocL33 CFSG.Certificates.Kernel.PkEnum

theorem qs_517101K : schP QSL = true ∧ orderV QSL = 32 := by
  constructor <;> decide +kernel

theorem le_517101K : (QSL.original.toList.all fun g => siftP L33.QA g 0) = true := by
  decide +kernel

theorem soc_517101K :
    (refCheck (elemsV QSL) l33Refs && sigmaCheck sl4 l33Refs && !siftP L33.QP sl4 0) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
