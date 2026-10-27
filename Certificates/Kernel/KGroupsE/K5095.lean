module

public import CFSG.GH74.GLS.Prop27.OddCoreCheck
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import CFSG.GH74.KGroups.L28Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

theorem odd_5095K : CFSG.GH74.GLS.Prop27.oddCoreCheck 189 (elemsV L28.QA) (elemsV L28.QP) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
