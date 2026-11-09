module

public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Chk
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.PermCent.SmallF3TwinSound
import Certificates.Kernel.PermCent.C6Hoist

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.OddStandard.SmallF3.Omega

theorem c6_442270K : c6free (elemsV L33.QA) (elemsV L33.QP) = true := by
  rw [← elemsT_eq_elemsV, ← elemsT_eq_elemsV, CFSG.Certificates.Kernel.PkCV.elemsT_eq_elemsC,
    CFSG.Certificates.Kernel.PkCV.elemsT_eq_elemsC, CFSG.Certificates.Kernel.PkCV.SmallF3T.c6free_C,
    CFSG.Certificates.Kernel.PkCV.SmallF3T.c6freeC_eq]
  decide +kernel

end CertificateChecks.KernelKGroupsE
