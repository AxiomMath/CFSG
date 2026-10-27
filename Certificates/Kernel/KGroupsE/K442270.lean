module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Chk
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.OddStandard.SmallF3.Omega

theorem c6_442270K : c6free (elemsV L33.QA) (elemsV L33.QP) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE
