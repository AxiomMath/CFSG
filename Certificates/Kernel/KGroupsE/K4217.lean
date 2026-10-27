module

public import Certificates.Data.A6B1
public import CFSG.GH74.KGroups.A6Inputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Quasithin.E217A6 CFSG.Certificates.Kernel.PkEnum

theorem a6_4217K : a6Check (elemsV A6.QP) (elemsV A6.QA) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
