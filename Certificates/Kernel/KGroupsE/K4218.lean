module

public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Data.L27B1
public import CFSG.GH74.KGroups.L27Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Quasithin.E217B1L27 CFSG.Certificates.Kernel.PkEnum

theorem l27_4218K : l27Check (elemsV L27.QP) = true := by decide +kernel

end CertificateChecks.KernelKGroupsE
